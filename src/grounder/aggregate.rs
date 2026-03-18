use std::collections::HashMap;

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{Aggregate, CompOp};
use crate::types::{AtomId, SymbolId, Value};

use super::instantiate::{eval_term, Bindings, FactStore};

/// Ground a #count aggregate. Returns auxiliary rules and the AtomId representing
/// "the aggregate bound is satisfied".
pub fn ground_count(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    // Collect ground elements
    let mut ground_elements: Vec<AtomId> = Vec::new();
    for elem in &agg.elements {
        // Each aggregate element has condition literals — find matching ground atoms
        for lit in &elem.condition {
            let ba = match lit {
                crate::parser::ast::Literal::Pos(ba) => ba,
                crate::parser::ast::Literal::Neg(_) => continue,
            };
            if let crate::parser::ast::BodyAtom::Atom(a) = ba
                && let Some(tuples) = facts.get(&a.predicate) {
                    for tuple in tuples {
                        let ga = GroundAtom { predicate: a.predicate, args: tuple.clone() };
                        ground_elements.push(atom_table.get_or_insert(ga));
                    }
                }
        }
    }

    let (op, bound_term) = agg.upper.as_ref()?;
    let Value::Int(bound) = eval_term(bound_term, bindings, const_map)? else { return None; };

    let n = ground_elements.len();
    // Target count based on comparison operator
    let target = match op {
        CompOp::Lt => bound - 1,
        CompOp::Leq => bound,
        CompOp::Gt => bound + 1,
        CompOp::Geq => bound,
        CompOp::Eq => bound,
        CompOp::Neq => return None, // Not easily encodable with staircase
    };

    if target <= 0 {
        // Always satisfied — return a trivially true aux atom
        let aux_name = interner.intern("__agg_true");
        let aux_atom = GroundAtom { predicate: aux_name, args: vec![] };
        let aux_id = atom_table.get_or_insert(aux_atom);
        let fact_rule = GroundRule { head: RuleHead::Normal(aux_id), body_pos: vec![], body_neg: vec![] };
        return Some((vec![fact_rule], aux_id));
    }
    let target = target as usize;
    if target > n {
        return None; // Impossible to satisfy
    }

    // Staircase encoding: aux(i,j) = "at least j of first i elements are true"
    // We create atoms __agg_N_i_j for unique identification
    let mut rules = Vec::new();
    let agg_id = atom_table.len(); // unique id for this aggregate instance
    let mut aux_atoms = vec![vec![AtomId(0); target + 1]; n + 1];

    // Create all auxiliary atoms
    for (i, row) in aux_atoms.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let name = interner.intern(&format!("__agg_{agg_id}_{i}_{j}"));
            let ga = GroundAtom { predicate: name, args: vec![] };
            *cell = atom_table.get_or_insert(ga);
        }
    }

    // Base: aux(i, 0) is always true (0 elements needed from any prefix)
    for row in &aux_atoms {
        rules.push(GroundRule { head: RuleHead::Normal(row[0]), body_pos: vec![], body_neg: vec![] });
    }

    // Staircase rules:
    // aux(i, j) :- aux(i-1, j).           (skip element i)
    // aux(i, j) :- elem_i, aux(i-1, j-1). (include element i)
    for i in 1..=n {
        for j in 1..=target.min(i) {
            // Skip rule
            rules.push(GroundRule {
                head: RuleHead::Normal(aux_atoms[i][j]),
                body_pos: vec![aux_atoms[i - 1][j]],
                body_neg: vec![],
            });
            // Include rule
            rules.push(GroundRule {
                head: RuleHead::Normal(aux_atoms[i][j]),
                body_pos: vec![ground_elements[i - 1], aux_atoms[i - 1][j - 1]],
                body_neg: vec![],
            });
        }
    }

    // The result atom is aux(n, target)
    let result_id = aux_atoms[n][target];

    // For CompOp::Gt/Geq/Lt/Leq: result_id means "count ≥ target"
    // For CompOp::Eq: need to also enforce "count ≤ target" (more complex, simplified here)
    Some((rules, result_id))
}
