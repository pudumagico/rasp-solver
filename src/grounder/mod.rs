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
fn expand_pools(program: &Program, const_map: &HashMap<SymbolId, Value>) -> Program {
    let mut stmts = Vec::new();
    for stmt in &program.statements {
        match stmt {
            Statement::Rule(r) => {
                // Expand ranges in head atoms of facts (empty body)
                if r.body.is_empty() {
                    let expanded_heads = expand_atom_list_ranges(&r.head, const_map);
                    for heads in expanded_heads {
                        stmts.push(Statement::Rule(ast::Rule { head: heads, body: r.body.clone() }));
                    }
                } else {
                    stmts.push(stmt.clone());
                }
            }
            _ => stmts.push(stmt.clone()),
        }
    }
    Program { statements: stmts }
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

/// Expand a single term: Range(a,b) → [Integer(a), ..., Integer(b)], others → [self]
fn expand_single_term(term: &Term, const_map: &HashMap<SymbolId, Value>) -> Vec<Term> {
    if let Term::Range(lo, hi) = term {
        let lo_val = eval_term(lo, &HashMap::new(), const_map);
        let hi_val = eval_term(hi, &HashMap::new(), const_map);
        if let (Some(Value::Int(a)), Some(Value::Int(b))) = (lo_val, hi_val) {
            return (a..=b).map(Term::Integer).collect();
        }
    }
    vec![term.clone()]
}

/// Collect #const definitions into a map.
fn collect_constants(program: &Program, _interner: &mut Interner) -> HashMap<SymbolId, Value> {
    let mut map = HashMap::new();
    for stmt in &program.statements {
        if let Statement::Const(c) = stmt
            && let Some(val) = eval_term(&c.value, &HashMap::new(), &map) {
                map.insert(c.name, val);
            }
    }
    map
}

/// Ground optimization directives. Returns (weighted_atoms, is_minimize) pairs.
pub fn ground_optimize(
    program: &Program,
    ground: &GroundProgram,
    _interner: &Interner,
) -> Vec<(Vec<(i64, AtomId)>, bool)> {
    let const_map = HashMap::new();
    let mut results = Vec::new();
    for stmt in &program.statements {
        if let Statement::Optimize(opt) = stmt {
            let mut weighted = Vec::new();
            for elem in &opt.elements {
                let Some(Value::Int(w)) = eval_term(&elem.weight, &HashMap::new(), &const_map) else { continue; };
                // Find atoms matching the condition
                for lit in &elem.condition {
                    let ba = match lit {
                        crate::parser::ast::Literal::Pos(ba) => ba,
                        _ => continue,
                    };
                    if let crate::parser::ast::BodyAtom::Atom(a) = ba {
                        // Find all ground atoms matching this predicate
                        for i in 0..ground.atom_table.len() {
                            let atom = ground.atom_table.resolve(AtomId(i as u32));
                            if atom.predicate == a.predicate {
                                weighted.push((w, AtomId(i as u32)));
                            }
                        }
                    }
                }
            }
            results.push((weighted, opt.minimize));
        }
    }
    results
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
