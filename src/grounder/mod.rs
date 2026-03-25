pub mod aggregate;
pub mod domain;
pub mod instantiate;
pub mod scc;
pub mod seminaive;

use std::collections::HashMap;

use crate::ground::program::GroundProgram;
use crate::interner::Interner;
use crate::parser::ast::{self, Program, Statement, Term};
use crate::types::{AtomId, SymbolId, Value};

use instantiate::eval_term;

#[derive(Debug, thiserror::Error)]
pub enum GroundError {
    #[error("unstratifiable program: {0}")]
    Unstratifiable(String),
    #[error("grounding error: {0}")]
    Other(String),
}

pub fn ground(program: &Program, interner: &mut Interner) -> Result<GroundProgram, GroundError> {
    let const_map = collect_constants(program, interner);
    let expanded = expand_pools(program, &const_map);
    let strata = scc::stratify(&expanded).map_err(GroundError::Unstratifiable)?;
    let mut gp = seminaive::evaluate(&strata, &expanded, interner, &const_map);
    seminaive::dedup_rules(&mut gp.rules);
    Ok(gp)
}

/// Expand range terms (pools) like `p(1..3)` into multiple statements.
/// Handles facts, rules, constraints, and choice rules.
fn expand_pools(program: &Program, const_map: &HashMap<SymbolId, Value>) -> Program {
    let mut stmts = Vec::new();
    for stmt in &program.statements {
        match stmt {
            Statement::Rule(r) => {
                let expanded_heads = expand_atom_list_ranges(&r.head, const_map);
                let expanded_bodies = expand_body_ranges(&r.body, const_map);
                for heads in &expanded_heads {
                    for body in &expanded_bodies {
                        stmts.push(Statement::Rule(ast::Rule { head: heads.clone(), body: body.clone() }));
                    }
                }
            }
            Statement::Constraint(c) => {
                let expanded_bodies = expand_body_ranges(&c.body, const_map);
                for body in expanded_bodies {
                    stmts.push(Statement::Constraint(ast::Constraint { body }));
                }
            }
            Statement::Choice(ch) => {
                // Expand ranges in choice element atoms and body
                let expanded_bodies = expand_body_ranges(&ch.body, const_map);
                let expanded_elems = expand_choice_elements(&ch.elements, const_map);
                for body in &expanded_bodies {
                    stmts.push(Statement::Choice(ast::ChoiceRule {
                        lower: ch.lower.clone(),
                        upper: ch.upper.clone(),
                        elements: expanded_elems.clone(),
                        body: body.clone(),
                    }));
                }
            }
            _ => stmts.push(stmt.clone()),
        }
    }
    Program { statements: stmts }
}

/// Expand pools/ranges in body literals.
/// Body pools are conjunctive: `p(a;b)` means `p(a), p(b)` — all variants
/// are included in a single body (not a cross-product of alternatives).
fn expand_body_ranges(body: &[ast::Literal], const_map: &HashMap<SymbolId, Value>) -> Vec<Vec<ast::Literal>> {
    let mut result = Vec::new();
    for lit in body {
        let expanded = expand_literal_ranges(lit, const_map);
        result.extend(expanded);
    }
    vec![reorder_body_interleave_comparisons(result)]
}

/// Reorder body literals:
/// 1. Multi-arg atoms before their single-arg component atoms (subsumption)
/// 2. Remove redundant single-arg atoms subsumed by multi-arg atoms
/// 3. Place comparisons immediately after the atom that binds their last variable
fn reorder_body_interleave_comparisons(body: Vec<ast::Literal>) -> Vec<ast::Literal> {
    use std::collections::HashSet;
    let mut atoms: Vec<ast::Literal> = Vec::new();
    let mut comps: Vec<ast::Literal> = Vec::new();
    let mut others: Vec<ast::Literal> = Vec::new();
    for lit in body {
        match &lit {
            ast::Literal::Pos(ast::BodyAtom::Comparison(_))
            | ast::Literal::Neg(ast::BodyAtom::Comparison(_)) => comps.push(lit),
            ast::Literal::Pos(ast::BodyAtom::Atom(_))
            | ast::Literal::Neg(ast::BodyAtom::Atom(_)) => atoms.push(lit),
            _ => others.push(lit),
        }
    }
    if comps.is_empty() && atoms.len() <= 1 { atoms.extend(others); return atoms; }

    // Separate multi-arg atoms (arity >= 2) from single-arg atoms (arity 1)
    let mut multi_atoms: Vec<ast::Literal> = Vec::new();
    let mut single_atoms: Vec<ast::Literal> = Vec::new();
    for lit in &atoms {
        if let ast::Literal::Pos(ast::BodyAtom::Atom(a)) | ast::Literal::Neg(ast::BodyAtom::Atom(a)) = lit {
            if a.args.len() >= 2 { multi_atoms.push(lit.clone()); }
            else { single_atoms.push(lit.clone()); }
        } else {
            single_atoms.push(lit.clone());
        }
    }

    // Find which variables are bound by multi-arg atoms
    let mut multi_bound: HashSet<SymbolId> = HashSet::new();
    for lit in &multi_atoms {
        if let ast::Literal::Pos(ast::BodyAtom::Atom(a)) | ast::Literal::Neg(ast::BodyAtom::Atom(a)) = lit {
            for arg in &a.args { collect_vars(arg, &mut multi_bound); }
        }
    }

    // Keep original atom order (multi-arg-first reordering disabled — interacts
    // badly with alldifferent injection for some programs)
    let ordered_atoms: Vec<ast::Literal> = atoms;

    // Interleave comparisons with atoms. Two strategies:
    // 1. After each atom: place comparisons whose variables are all now bound
    // 2. Before an atom: if a comparison has exactly ONE free variable that
    //    the atom would bind, and the comparison is an equality that can solve
    //    for that variable, place the comparison BEFORE the atom (so the atom
    //    becomes a check instead of an enumeration)
    let mut bound_vars: HashSet<SymbolId> = HashSet::new();
    let mut result = Vec::with_capacity(ordered_atoms.len() + comps.len() + others.len());
    let mut placed = vec![false; comps.len()];

    for atom_lit in &ordered_atoms {
        // Strategy 2 disabled: equality-before-atom reordering interacts badly
        // with alldifferent injection, causing incorrect UNSAT on some programs.

        if let ast::Literal::Pos(ast::BodyAtom::Atom(a)) | ast::Literal::Neg(ast::BodyAtom::Atom(a)) = atom_lit {
            for arg in &a.args { collect_vars(arg, &mut bound_vars); }
        }
        result.push(atom_lit.clone());
        for (ci, comp) in comps.iter().enumerate() {
            if placed[ci] { continue; }
            if lit_vars(comp).is_subset(&bound_vars) {
                result.push(comp.clone());
                placed[ci] = true;
            }
        }
    }
    for (ci, comp) in comps.into_iter().enumerate() {
        if !placed[ci] { result.push(comp); }
    }
    result.extend(others);
    result
}

fn collect_vars(term: &ast::Term, vars: &mut std::collections::HashSet<SymbolId>) {
    match term {
        ast::Term::Variable(v) => { vars.insert(*v); }
        ast::Term::BinOp(_, l, r) => { collect_vars(l, vars); collect_vars(r, vars); }
        ast::Term::UnaryMinus(t) | ast::Term::Abs(t) => collect_vars(t, vars),
        ast::Term::Function(_, args) => args.iter().for_each(|a| collect_vars(a, vars)),
        ast::Term::Pool(ts) => ts.iter().for_each(|t| collect_vars(t, vars)),
        ast::Term::Range(a, b) => { collect_vars(a, vars); collect_vars(b, vars); }
        _ => {}
    }
}

fn lit_vars(lit: &ast::Literal) -> std::collections::HashSet<SymbolId> {
    let mut vars = std::collections::HashSet::new();
    match lit {
        ast::Literal::Pos(ba) | ast::Literal::Neg(ba) => match ba {
            ast::BodyAtom::Comparison(c) => {
                collect_vars(&c.left, &mut vars);
                collect_vars(&c.right, &mut vars);
            }
            ast::BodyAtom::Atom(a) => a.args.iter().for_each(|t| collect_vars(t, &mut vars)),
            _ => {}
        }
    }
    vars
}

/// Expand ranges within a single literal.
fn expand_literal_ranges(lit: &ast::Literal, const_map: &HashMap<SymbolId, Value>) -> Vec<ast::Literal> {
    match lit {
        ast::Literal::Pos(ast::BodyAtom::Atom(a)) => {
            expand_atom_ranges(a, const_map).into_iter()
                .map(|ea| ast::Literal::Pos(ast::BodyAtom::Atom(ea)))
                .collect()
        }
        ast::Literal::Neg(ast::BodyAtom::Atom(a)) => {
            expand_atom_ranges(a, const_map).into_iter()
                .map(|ea| ast::Literal::Neg(ast::BodyAtom::Atom(ea)))
                .collect()
        }
        _ => vec![lit.clone()],
    }
}

/// Expand ranges in choice elements.
fn expand_choice_elements(elems: &[ast::ChoiceElement], const_map: &HashMap<SymbolId, Value>) -> Vec<ast::ChoiceElement> {
    let mut result = Vec::new();
    for elem in elems {
        let expanded_atoms = expand_atom_ranges(&elem.atom, const_map);
        for ea in expanded_atoms {
            result.push(ast::ChoiceElement { atom: ea, condition: elem.condition.clone() });
        }
    }
    result
}

/// Expand ranges in a list of atoms. Returns all combinations.
/// e.g., [p(1..2, a)] → [[p(1,a)], [p(2,a)]]
fn expand_atom_list_ranges(
    atoms: &[ast::Atom],
    const_map: &HashMap<SymbolId, Value>,
) -> Vec<Vec<ast::Atom>> {
    if atoms.len() == 1 {
        return expand_atom_ranges(&atoms[0], const_map)
            .into_iter()
            .map(|a| vec![a])
            .collect();
    }
    // For disjunctive heads, expand each atom independently
    let mut result = vec![Vec::new()];
    for atom in atoms {
        let expansions = expand_atom_ranges(atom, const_map);
        let mut new_result = Vec::new();
        for existing in &result {
            for exp in &expansions {
                let mut combined = existing.clone();
                combined.push(exp.clone());
                new_result.push(combined);
            }
        }
        result = new_result;
    }
    result
}

/// Expand ranges in atom arguments. `p(1..3, a)` → [p(1,a), p(2,a), p(3,a)]
fn expand_atom_ranges(atom: &ast::Atom, const_map: &HashMap<SymbolId, Value>) -> Vec<ast::Atom> {
    let expanded_args = expand_term_list_ranges(&atom.args, const_map);
    expanded_args.into_iter()
        .map(|args| ast::Atom { predicate: atom.predicate, args })
        .collect()
}

/// Expand ranges in a term list. Each Range(a,b) produces multiple alternatives.
fn expand_term_list_ranges(terms: &[Term], const_map: &HashMap<SymbolId, Value>) -> Vec<Vec<Term>> {
    let mut result = vec![Vec::new()];
    for term in terms {
        let alternatives = expand_single_term(term, const_map);
        let mut new_result = Vec::new();
        for existing in &result {
            for alt in &alternatives {
                let mut combined = existing.clone();
                combined.push(alt.clone());
                new_result.push(combined);
            }
        }
        result = new_result;
    }
    result
}

/// Expand a single term: Range(a,b) → [Integer(a), ..., Integer(b)],
/// Pool([t1,t2,...]) → [t1, t2, ...] (recursively expanded), others → [self]
fn expand_single_term(term: &Term, const_map: &HashMap<SymbolId, Value>) -> Vec<Term> {
    match term {
        Term::Range(lo, hi) => {
            let empty = instantiate::Bindings::new();
            let lo_val = eval_term(lo, &empty, const_map);
            let hi_val = eval_term(hi, &empty, const_map);
            if let (Some(Value::Int(a)), Some(Value::Int(b))) = (lo_val, hi_val) {
                return (a..=b).map(Term::Integer).collect();
            }
            vec![term.clone()]
        }
        Term::Pool(terms) => terms.iter()
            .flat_map(|t| expand_single_term(t, const_map))
            .collect(),
        _ => vec![term.clone()],
    }
}

/// Collect #const definitions into a map.
fn collect_constants(program: &Program, _interner: &mut Interner) -> HashMap<SymbolId, Value> {
    let mut map = HashMap::new();
    for stmt in &program.statements {
        if let Statement::Const(c) = stmt
            && let Some(val) = eval_term(&c.value, &instantiate::Bindings::new(), &map) {
                map.insert(c.name, val);
            }
    }
    map
}

/// A single optimization specification at a given priority level.
pub struct OptSpec {
    pub priority: i64,
    pub weighted: Vec<(i64, AtomId)>,
    pub minimize: bool,
}

/// Ground optimization directives. Returns per-priority-level specs sorted by
/// descending priority (highest priority = optimized first).
pub fn ground_optimize(
    program: &Program,
    ground: &GroundProgram,
    _interner: &Interner,
) -> Vec<OptSpec> {
    let const_map = HashMap::new();
    // Collect all weighted atoms grouped by (priority, minimize)
    let mut by_priority: HashMap<(i64, bool), Vec<(i64, AtomId)>> = HashMap::new();
    for stmt in &program.statements {
        if let Statement::Optimize(opt) = stmt {
            for elem in &opt.elements {
                let empty = instantiate::Bindings::new();
                let Some(Value::Int(w)) = eval_term(&elem.weight, &empty, &const_map) else { continue; };
                let priority = elem.priority.as_ref()
                    .and_then(|t| eval_term(t, &empty, &const_map))
                    .and_then(|v| if let Value::Int(p) = v { Some(p) } else { None })
                    .unwrap_or(0);
                for lit in &elem.condition {
                    let ba = match lit {
                        crate::parser::ast::Literal::Pos(ba) => ba,
                        _ => continue,
                    };
                    if let crate::parser::ast::BodyAtom::Atom(a) = ba {
                        for i in 0..ground.atom_table.len() {
                            let atom = ground.atom_table.resolve(AtomId(i as u32));
                            if atom.predicate == a.predicate {
                                by_priority.entry((priority, opt.minimize))
                                    .or_default()
                                    .push((w, AtomId(i as u32)));
                            }
                        }
                    }
                }
            }
        }
    }
    let mut specs: Vec<OptSpec> = by_priority.into_iter()
        .map(|((priority, minimize), weighted)| OptSpec { priority, weighted, minimize })
        .collect();
    // Sort descending by priority (highest first for lexicographic optimization)
    specs.sort_by(|a, b| b.priority.cmp(&a.priority));
    specs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    #[test]
    fn ground_simple() {
        let mut interner = Interner::new();
        let prog = parser::parse("a. b :- a.", &mut interner).unwrap();
        let gp = ground(&prog, &mut interner).unwrap();
        assert!(gp.atom_table.len() >= 2);
    }

    #[test]
    fn ground_with_const() {
        let mut interner = Interner::new();
        let prog = parser::parse("#const n = 3. p(n).", &mut interner).unwrap();
        let gp = ground(&prog, &mut interner).unwrap();
        assert_eq!(gp.atom_table.len(), 1);
        let atom = gp.atom_table.resolve(crate::types::AtomId(0));
        assert_eq!(atom.args[0], Value::Int(3));
    }
}
