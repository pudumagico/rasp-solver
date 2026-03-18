use std::collections::{HashMap, HashSet};

use crate::parser::ast::{self, BodyAtom, Literal, Statement};
use crate::types::SymbolId;

/// One stratum: a set of predicates to evaluate together, and the rule indices.
pub struct Stratum {
    pub predicates: HashSet<SymbolId>,
    pub rule_indices: Vec<usize>,
}

/// Compute stratification from the program's predicate dependency graph.
/// Returns strata in bottom-up evaluation order.
/// Programs with negative cycles within an SCC are allowed — the solver's
/// unfounded set detection handles stable model semantics for these cases.
pub fn stratify(program: &ast::Program) -> Result<Vec<Stratum>, String> {
    let (nodes, edges) = build_dep_graph(program);
    let sccs = tarjan(&nodes, &edges);
    // Assign rules to strata
    let mut pred_to_stratum = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for &pred in &scc.predicates {
            pred_to_stratum.insert(pred, i);
        }
    }
    let mut strata: Vec<Stratum> = sccs.into_iter().map(|s| Stratum { predicates: s.predicates, rule_indices: Vec::new() }).collect();
    for (i, stmt) in program.statements.iter().enumerate() {
        let head_pred = match stmt {
            Statement::Rule(r) => Some(r.head.predicate),
            Statement::Choice(ch) => ch.elements.first().map(|e| e.atom.predicate),
            Statement::Constraint(_) => None,
            _ => continue,
        };
        if let Some(pred) = head_pred {
            if let Some(&si) = pred_to_stratum.get(&pred) {
                strata[si].rule_indices.push(i);
            }
        } else if matches!(stmt, Statement::Constraint(_)) {
            // Constraints go in the last stratum
            if let Some(last) = strata.last_mut() {
                last.rule_indices.push(i);
            }
        }
    }
    Ok(strata)
}

type DepEdges = HashMap<SymbolId, Vec<(SymbolId, bool)>>;

/// Build predicate dependency graph.
/// Returns (all_nodes, adjacency_list) where edges are (target, is_negative).
fn build_dep_graph(program: &ast::Program) -> (HashSet<SymbolId>, DepEdges) {
    let mut nodes = HashSet::new();
    let mut edges = HashMap::<SymbolId, Vec<(SymbolId, bool)>>::new();
    for stmt in &program.statements {
        match stmt {
            Statement::Rule(r) => {
                let head = r.head.predicate;
                nodes.insert(head);
                add_body_edges(head, &r.body, &mut nodes, &mut edges);
            }
            Statement::Choice(ch) => {
                for elem in &ch.elements {
                    let head = elem.atom.predicate;
                    nodes.insert(head);
                    add_body_edges(head, &ch.body, &mut nodes, &mut edges);
                }
            }
            Statement::Constraint(c) => {
                // Constraints depend on their body predicates but have no head.
                for lit in &c.body {
                    if let Some(pred) = lit_predicate(lit) {
                        nodes.insert(pred);
                    }
                }
            }
            _ => {}
        }
    }
    (nodes, edges)
}

fn add_body_edges(
    head: SymbolId,
    body: &[Literal],
    nodes: &mut HashSet<SymbolId>,
    edges: &mut DepEdges,
) {
    for lit in body {
        let (pred, negative) = match lit {
            Literal::Pos(ba) => (body_atom_pred(ba), false),
            Literal::Neg(ba) => (body_atom_pred(ba), true),
        };
        if let Some(p) = pred {
            nodes.insert(p);
            edges.entry(head).or_default().push((p, negative));
        }
    }
}

fn body_atom_pred(ba: &BodyAtom) -> Option<SymbolId> {
    match ba {
        BodyAtom::Atom(a) => Some(a.predicate),
        _ => None,
    }
}

fn lit_predicate(lit: &Literal) -> Option<SymbolId> {
    match lit {
        Literal::Pos(ba) | Literal::Neg(ba) => body_atom_pred(ba),
    }
}

// ── Tarjan's SCC ───────────────────────────────────────────

struct SccState {
    index_counter: u32,
    stack: Vec<SymbolId>,
    on_stack: HashSet<SymbolId>,
    indices: HashMap<SymbolId, u32>,
    lowlinks: HashMap<SymbolId, u32>,
    result: Vec<SccSet>,
}

struct SccSet {
    predicates: HashSet<SymbolId>,
}

fn tarjan(
    nodes: &HashSet<SymbolId>,
    edges: &DepEdges,
) -> Vec<SccSet> {
    let mut state = SccState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        indices: HashMap::new(),
        lowlinks: HashMap::new(),
        result: Vec::new(),
    };
    for &node in nodes {
        if !state.indices.contains_key(&node) {
            strongconnect(node, edges, &mut state);
        }
    }
    // Tarjan emits SCCs in dependency-first (bottom-up) order: sinks first.
    state.result
}

fn strongconnect(
    v: SymbolId,
    edges: &DepEdges,
    state: &mut SccState,
) {
    let idx = state.index_counter;
    state.index_counter += 1;
    state.indices.insert(v, idx);
    state.lowlinks.insert(v, idx);
    state.stack.push(v);
    state.on_stack.insert(v);

    if let Some(neighbors) = edges.get(&v) {
        for &(w, _) in neighbors {
            if !state.indices.contains_key(&w) {
                strongconnect(w, edges, state);
                let wl = state.lowlinks[&w];
                let vl = state.lowlinks.get_mut(&v).unwrap();
                if wl < *vl { *vl = wl; }
            } else if state.on_stack.contains(&w) {
                let wi = state.indices[&w];
                let vl = state.lowlinks.get_mut(&v).unwrap();
                if wi < *vl { *vl = wi; }
            }
        }
    }

    if state.lowlinks[&v] == state.indices[&v] {
        let mut scc = HashSet::new();
        loop {
            let w = state.stack.pop().unwrap();
            state.on_stack.remove(&w);
            scc.insert(w);
            if w == v { break; }
        }
        state.result.push(SccSet { predicates: scc });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::parser;

    #[test]
    fn simple_stratification() {
        let mut interner = Interner::new();
        let prog = parser::parse("a. b :- a. c :- b.", &mut interner).unwrap();
        let strata = stratify(&prog).unwrap();
        // Should have at least 1 stratum; all predicates should appear
        let all_preds: HashSet<_> = strata.iter().flat_map(|s| &s.predicates).copied().collect();
        assert!(all_preds.contains(&interner.intern("a")));
        assert!(all_preds.contains(&interner.intern("b")));
        assert!(all_preds.contains(&interner.intern("c")));
    }

    #[test]
    fn stratification_with_negation() {
        let mut interner = Interner::new();
        let prog = parser::parse("a. b :- not a.", &mut interner).unwrap();
        let strata = stratify(&prog).unwrap();
        // `a` and `b` are in different strata since b depends negatively on a
        let a_id = interner.intern("a");
        let b_id = interner.intern("b");
        let a_stratum = strata.iter().position(|s| s.predicates.contains(&a_id)).unwrap();
        let b_stratum = strata.iter().position(|s| s.predicates.contains(&b_id)).unwrap();
        assert!(a_stratum < b_stratum);
    }
}
