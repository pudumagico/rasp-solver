use std::collections::HashMap;

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{Aggregate, AggFunction, CompOp};
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

    Some((rules, result_id))
}

/// Ground a #sum aggregate. Elements have weights; the sum of weights of true
/// elements is compared against a bound.
pub fn ground_sum(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    // Collect (weight, atom_id) pairs from aggregate elements
    let mut weighted_elements: Vec<(i64, AtomId)> = Vec::new();
    for elem in &agg.elements {
        // First term in the element is the weight
        let weight = if let Some(first_term) = elem.terms.first() {
            match eval_term(first_term, bindings, const_map)? {
                Value::Int(w) => w,
                _ => 1,
            }
        } else {
            1
        };
        // Condition atoms
        for lit in &elem.condition {
            let ba = match lit {
                crate::parser::ast::Literal::Pos(ba) => ba,
                _ => continue,
            };
            if let crate::parser::ast::BodyAtom::Atom(a) = ba
                && let Some(tuples) = facts.get(&a.predicate) {
                    for tuple in tuples {
                        let ga = GroundAtom { predicate: a.predicate, args: tuple.clone() };
                        weighted_elements.push((weight, atom_table.get_or_insert(ga)));
                    }
                }
        }
    }

    let (op, bound_term) = agg.upper.as_ref()?;
    let Value::Int(bound) = eval_term(bound_term, bindings, const_map)? else { return None; };

    let target = match op {
        CompOp::Lt => bound - 1,
        CompOp::Leq => bound,
        CompOp::Gt => bound + 1,
        CompOp::Geq => bound,
        CompOp::Eq => bound,
        CompOp::Neq => return None,
    };

    if target <= 0 {
        let aux_name = interner.intern("__sum_true");
        let aux_atom = GroundAtom { predicate: aux_name, args: vec![] };
        let aux_id = atom_table.get_or_insert(aux_atom);
        return Some((vec![GroundRule { head: RuleHead::Normal(aux_id), body_pos: vec![], body_neg: vec![] }], aux_id));
    }
    let target = target as usize;

    // Knapsack-style DP encoding:
    // aux(i, w) = "sum of first i elements that are true is >= w"
    let n = weighted_elements.len();
    let max_sum: usize = weighted_elements.iter().map(|(w, _)| (*w).max(0) as usize).sum();
    let cap = target.min(max_sum);
    if cap == 0 || target > max_sum { return None; }

    let mut rules = Vec::new();
    let agg_id = atom_table.len();

    // Create auxiliary atoms: aux(i, w) for i in 0..=n, w in 0..=cap
    let mut aux = vec![vec![AtomId(0); cap + 1]; n + 1];
    for (i, row) in aux.iter_mut().enumerate() {
        for (w, cell) in row.iter_mut().enumerate() {
            let name = interner.intern(&format!("__sum_{agg_id}_{i}_{w}"));
            *cell = atom_table.get_or_insert(GroundAtom { predicate: name, args: vec![] });
        }
    }

    // Base: aux(i, 0) always true
    for row in &aux {
        rules.push(GroundRule { head: RuleHead::Normal(row[0]), body_pos: vec![], body_neg: vec![] });
    }

    // DP transitions:
    // aux(i, w) :- aux(i-1, w).  (skip element i)
    // aux(i, w) :- elem_i, aux(i-1, w - weight_i).  (include element i)
    for i in 1..=n {
        let (wi, elem_id) = weighted_elements[i - 1];
        let wi = wi.max(0) as usize;
        for w in 1..=cap {
            // Skip
            rules.push(GroundRule {
                head: RuleHead::Normal(aux[i][w]),
                body_pos: vec![aux[i - 1][w]],
                body_neg: vec![],
            });
            // Include (if w >= weight_i)
            if wi > 0 && w >= wi {
                rules.push(GroundRule {
                    head: RuleHead::Normal(aux[i][w]),
                    body_pos: vec![elem_id, aux[i - 1][w - wi]],
                    body_neg: vec![],
                });
            }
        }
    }

    Some((rules, aux[n][cap]))
}

/// Dispatch aggregate grounding based on function type.
pub fn ground_aggregate(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    match agg.function {
        AggFunction::Count => ground_count(agg, bindings, facts, atom_table, interner, const_map),
        AggFunction::Sum => ground_sum(agg, bindings, facts, atom_table, interner, const_map),
        AggFunction::Min | AggFunction::Max => None, // TODO
    }
}
