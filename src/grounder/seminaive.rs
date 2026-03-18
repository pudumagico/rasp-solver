use std::collections::{HashMap, HashSet};

use crate::ground::program::{AtomTable, GroundAtom, GroundProgram, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{self, Statement, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::instantiate::{self, FactStore};
use super::scc::Stratum;

/// Fast lookup set for checking if a fact tuple already exists.
type FactSet = HashMap<SymbolId, HashSet<Vec<Value>>>;

fn fact_set_from_store(store: &FactStore) -> FactSet {
    store.iter().map(|(k, v)| (*k, v.iter().cloned().collect())).collect()
}

fn add_to_both(
    pred: SymbolId,
    args: Vec<Value>,
    facts: &mut FactStore,
    known: &mut FactSet,
) -> bool {
    if known.entry(pred).or_default().insert(args.clone()) {
        facts.entry(pred).or_default().push(args);
        true
    } else {
        false
    }
}

/// Run semi-naive bottom-up evaluation across strata.
pub fn evaluate(
    strata: &[Stratum],
    program: &ast::Program,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> GroundProgram {
    let mut atom_table = AtomTable::new();
    let mut all_rules: Vec<GroundRule> = Vec::new();
    let mut facts = FactStore::new();
    let mut known = FactSet::new();
    let mut show_atoms = Vec::new();
    let mut show_all = true;

    for stmt in &program.statements {
        match stmt {
            Statement::ShowSig(_) => { show_all = false; }
            Statement::Show(_) => { show_all = false; }
            _ => {}
        }
    }

    // Collect initial facts (rules with empty body and single head atom)
    for stmt in &program.statements {
        if let Statement::Rule(r) = stmt
            && r.body.is_empty() && r.head.len() == 1 {
                let h = &r.head[0];
                let args: Option<Vec<Value>> = h.args.iter()
                    .map(|t| instantiate::eval_term(t, &HashMap::new(), const_map))
                    .collect();
                if let Some(args) = args
                    && add_to_both(h.predicate, args.clone(), &mut facts, &mut known) {
                        let ga = GroundAtom { predicate: h.predicate, args };
                        let id = atom_table.get_or_insert(ga);
                        all_rules.push(GroundRule { head: RuleHead::Normal(id), body_pos: vec![], body_neg: vec![] });
                    }
            }
    }

    for stratum in strata {
        evaluate_stratum(
            stratum, program, &mut facts, &mut known, &mut atom_table,
            &mut all_rules, interner, const_map,
        );
    }

    // Resolve show atoms
    if !show_all {
        for stmt in &program.statements {
            if let Statement::ShowSig(s) = stmt {
                for i in 0..atom_table.len() {
                    let atom = atom_table.resolve(crate::types::AtomId(i as u32));
                    if atom.predicate == s.predicate && atom.args.len() == s.arity {
                        show_atoms.push(crate::types::AtomId(i as u32));
                    }
                }
            }
        }
    }

    GroundProgram { atom_table, rules: all_rules, show_atoms, show_all }
}

#[allow(clippy::too_many_arguments)]
fn evaluate_stratum(
    stratum: &Stratum,
    program: &ast::Program,
    facts: &mut FactStore,
    known: &mut FactSet,
    atom_table: &mut AtomTable,
    all_rules: &mut Vec<GroundRule>,
    _interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) {
    const MAX_ITERATIONS: usize = 10_000;

    let mut normal_rules = Vec::new();
    let mut constraints = Vec::new();
    let mut choices = Vec::new();

    for &ri in &stratum.rule_indices {
        match &program.statements[ri] {
            Statement::Rule(r) if !r.body.is_empty() || r.head.len() > 1 => normal_rules.push(r),
            Statement::Constraint(c) => constraints.push(c),
            Statement::Choice(ch) => choices.push(ch),
            _ => {} // single-head facts already collected
        }
    }

    // 1. Ground choice rules first so their atoms enter the domain
    for ch in &choices {
        let ground_rules = instantiate::instantiate_choice(ch, facts, atom_table, const_map);
        // Generate bound constraints for each grounded choice rule
        for gr in &ground_rules {
            if let RuleHead::Choice(heads) = &gr.head {
                let bound_constraints = generate_bound_constraints(
                    heads, &ch.lower, &ch.upper, &gr.body_pos, &gr.body_neg, const_map,
                );
                all_rules.extend(bound_constraints);
            }
        }
        all_rules.extend(ground_rules);
    }

    // 2. Build domain = facts + choice-defined atoms (for positive matching)
    let mut domain = facts.clone();
    let mut domain_known = fact_set_from_store(&domain);
    for rule in all_rules.iter() {
        if let RuleHead::Choice(heads) = &rule.head {
            for &head_id in heads {
                let head_atom = atom_table.resolve(head_id);
                add_to_both(head_atom.predicate, head_atom.args.clone(), &mut domain, &mut domain_known);
            }
        }
    }

    // 3. Semi-naive fixpoint using domain for positive matching, facts for NAF
    let mut seen_rules: HashSet<(Vec<u32>, Vec<u32>, Vec<u32>)> = HashSet::new();
    let mut changed = true;
    let mut iterations = 0;
    while changed && iterations < MAX_ITERATIONS {
        changed = false;
        iterations += 1;

        for rule in &normal_rules {
            let ground_rules = instantiate::instantiate_rule_with_domain(
                &rule.head, &rule.body, facts, &domain, atom_table, const_map,
            );
            for gr in ground_rules {
                let key = rule_key(&gr);
                if !seen_rules.insert(key) { continue; }

                let head_ids = match &gr.head {
                    RuleHead::Normal(id) => vec![*id],
                    RuleHead::Disjunction(ids) => ids.clone(),
                    _ => vec![],
                };
                for head_id in head_ids {
                    let head_atom = atom_table.resolve(head_id);
                    let pred = head_atom.predicate;
                    let args = head_atom.args.clone();
                    if add_to_both(pred, args.clone(), facts, known) {
                        changed = true;
                    }
                    add_to_both(pred, args, &mut domain, &mut domain_known);
                }
                all_rules.push(gr);
            }
        }
    }

    // Ground constraints
    for c in &constraints {
        let ground_rules = instantiate::instantiate_constraint(&c.body, facts, &domain, atom_table, const_map);
        all_rules.extend(ground_rules);
    }
}

/// Generate constraint rules to enforce choice rule bounds.
/// Lower bound L: at least L head atoms must be true (when body holds).
/// Upper bound U: at most U head atoms can be true (when body holds).
fn generate_bound_constraints(
    heads: &[AtomId],
    lower: &Option<Term>,
    upper: &Option<Term>,
    body_pos: &[AtomId],
    body_neg: &[AtomId],
    const_map: &HashMap<SymbolId, Value>,
) -> Vec<GroundRule> {
    let mut rules = Vec::new();
    let n = heads.len();

    let eval_bound = |term: &Term| -> Option<usize> {
        let val = instantiate::eval_term(term, &HashMap::new(), const_map)?;
        match val {
            Value::Int(v) if v >= 0 => Some(v as usize),
            _ => None,
        }
    };

    // Upper bound: at most U can be true → every (U+1)-subset must have a false atom
    // Constraint: `:- body, h1, h2, ..., h_{U+1}` for each (U+1)-subset
    if let Some(u_term) = upper
        && let Some(u) = eval_bound(u_term)
            && u < n {
                let subset_size = u + 1;
                for_each_subset(heads, subset_size, &mut |subset| {
                    let mut bp = body_pos.to_vec();
                    bp.extend_from_slice(subset);
                    rules.push(GroundRule { head: RuleHead::Constraint, body_pos: bp, body_neg: body_neg.to_vec() });
                });
            }

    // Lower bound: at least L must be true → constraint fires if fewer than L are true
    // Constraint: `:- body, not h1, not h2, ..., not h_{n-L+1}` for each (n-L+1)-subset
    // i.e., if n-L+1 atoms are false, the bound is violated
    if let Some(l_term) = lower
        && let Some(l) = eval_bound(l_term)
            && l > 0 {
                if l > n {
                    // Impossible: need more atoms than exist → always UNSAT when body holds
                    rules.push(GroundRule { head: RuleHead::Constraint, body_pos: body_pos.to_vec(), body_neg: body_neg.to_vec() });
                } else {
                    let false_count = n - l + 1;
                    for_each_subset(heads, false_count, &mut |subset| {
                        let mut bn = body_neg.to_vec();
                        bn.extend_from_slice(subset);
                        rules.push(GroundRule { head: RuleHead::Constraint, body_pos: body_pos.to_vec(), body_neg: bn });
                    });
                }
            }

    rules
}

/// Call `callback` with every k-element subset of `elems`.
fn for_each_subset(elems: &[AtomId], k: usize, callback: &mut impl FnMut(&[AtomId])) {
    if k == 0 {
        callback(&[]);
        return;
    }
    if k > elems.len() { return; }
    let mut indices: Vec<usize> = (0..k).collect();
    loop {
        let subset: Vec<AtomId> = indices.iter().map(|&i| elems[i]).collect();
        callback(&subset);
        // Advance to next combination
        let mut i = k;
        loop {
            if i == 0 { return; }
            i -= 1;
            indices[i] += 1;
            if indices[i] <= elems.len() - k + i { break; }
        }
        for j in (i + 1)..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
}

/// Deduplicate ground rules.
pub fn dedup_rules(rules: &mut Vec<GroundRule>) {
    let mut seen = HashSet::new();
    rules.retain(|r| seen.insert(rule_key(r)));
}

fn rule_key(r: &GroundRule) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let head = match &r.head {
        RuleHead::Normal(id) => vec![0, id.0],
        RuleHead::Disjunction(ids) => {
            let mut v = vec![1];
            v.extend(ids.iter().map(|id| id.0));
            v
        }
        RuleHead::Choice(ids) => {
            let mut v = vec![2];
            v.extend(ids.iter().map(|id| id.0));
            v
        }
        RuleHead::Constraint => vec![3],
    };
    let pos: Vec<u32> = r.body_pos.iter().map(|id| id.0).collect();
    let neg: Vec<u32> = r.body_neg.iter().map(|id| id.0).collect();
    (head, pos, neg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grounder::scc;
    use crate::parser;

    fn ground_program(input: &str) -> (GroundProgram, Interner) {
        let mut interner = Interner::new();
        let prog = parser::parse(input, &mut interner).unwrap();
        let strata = scc::stratify(&prog).unwrap();
        let gp = evaluate(&strata, &prog, &mut interner, &HashMap::new());
        (gp, interner)
    }

    #[test]
    fn ground_facts_only() {
        let (gp, _) = ground_program("a. b. c.");
        assert_eq!(gp.atom_table.len(), 3);
    }

    #[test]
    fn ground_transitive_closure() {
        let (gp, mut interner) = ground_program(
            "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). path(X,Z) :- path(X,Y), edge(Y,Z)."
        );
        let path_id = interner.intern("path");
        let path_atoms: Vec<_> = (0..gp.atom_table.len())
            .map(|i| gp.atom_table.resolve(crate::types::AtomId(i as u32)))
            .filter(|a| a.predicate == path_id)
            .collect();
        assert_eq!(path_atoms.len(), 3);
    }

    #[test]
    fn ground_with_negation() {
        let (gp, _) = ground_program("a. b :- not c.");
        assert!(gp.atom_table.len() >= 2);
    }

    #[test]
    fn ground_constraint() {
        let (gp, _) = ground_program("a. b. :- a, b.");
        assert!(gp.rules.iter().any(|r| matches!(r.head, RuleHead::Constraint)));
    }
}
