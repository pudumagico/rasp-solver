use std::collections::HashMap;

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{Aggregate, AggFunction, CompOp, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::instantiate::{eval_term, Bindings, FactStore};

/// Collect ground (weight, AtomId) pairs from aggregate elements.
/// Properly binds element-local variables by unifying condition atoms
/// with ground tuples from the fact store.
fn collect_weighted_elements(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    default_weight: i64,
) -> Vec<(i64, AtomId)> {
    let mut result = Vec::new();
    for elem in &agg.elements {
        for lit in &elem.condition {
            let ba = match lit {
                crate::parser::ast::Literal::Pos(ba) => ba,
                _ => continue,
            };
            if let crate::parser::ast::BodyAtom::Atom(a) = ba
                && let Some(tuples) = facts.get(&a.predicate)
            {
                for tuple in tuples {
                    if tuple.len() != a.args.len() { continue; }
                    // Unify condition atom args with tuple to bind element-local variables
                    let mut local_bindings = bindings.clone();
                    if !unify_args(&a.args, tuple, &mut local_bindings, const_map) {
                        continue;
                    }
                    // Evaluate weight with element-local bindings
                    let weight = if let Some(first_term) = elem.terms.first() {
                        match eval_term(first_term, &local_bindings, const_map) {
                            Some(Value::Int(w)) => w,
                            _ => default_weight,
                        }
                    } else {
                        default_weight
                    };
                    let ga = GroundAtom { predicate: a.predicate, args: tuple.clone() };
                    result.push((weight, atom_table.get_or_insert(ga)));
                }
            }
        }
    }
    result
}

/// Unify atom arguments with a ground tuple, extending bindings.
fn unify_args(
    args: &[Term],
    tuple: &[Value],
    bindings: &mut Bindings,
    const_map: &HashMap<SymbolId, Value>,
) -> bool {
    for (arg, val) in args.iter().zip(tuple.iter()) {
        match arg {
            Term::Variable(v) => {
                if let Some(existing) = bindings.get(v) {
                    if existing != val { return false; }
                } else {
                    bindings.insert(*v, val.clone());
                }
            }
            Term::Anonymous => {}
            _ => {
                if let Some(ground_val) = eval_term(arg, bindings, const_map) {
                    if &ground_val != val { return false; }
                } else {
                    return false;
                }
            }
        }
    }
    true
}

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
    let weighted = collect_weighted_elements(agg, bindings, facts, atom_table, const_map, 1);
    let ground_elements: Vec<AtomId> = weighted.into_iter().map(|(_, id)| id).collect();

    let (op, bound_term) = agg.upper.as_ref()?;
    let Value::Int(bound) = eval_term(bound_term, bindings, const_map)? else { return None; };

    let n = ground_elements.len();
    let target = match op {
        CompOp::Lt => bound - 1,
        CompOp::Leq => bound,
        CompOp::Gt => bound + 1,
        CompOp::Geq => bound,
        CompOp::Eq => bound,
        CompOp::Neq => return None,
    };

    if target <= 0 {
        let aux_name = interner.intern("__agg_true");
        let aux_atom = GroundAtom { predicate: aux_name, args: vec![] };
        let aux_id = atom_table.get_or_insert(aux_atom);
        return Some((vec![GroundRule { head: RuleHead::Normal(aux_id), body_pos: vec![], body_neg: vec![] }], aux_id));
    }
    let target = target as usize;
    if target > n { return None; }

    // Staircase encoding: aux(i,j) = "at least j of first i elements are true"
    let mut rules = Vec::new();
    let agg_id = atom_table.len();
    let mut aux_atoms = vec![vec![AtomId(0); target + 1]; n + 1];

    for (i, row) in aux_atoms.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let name = interner.intern(&format!("__agg_{agg_id}_{i}_{j}"));
            *cell = atom_table.get_or_insert(GroundAtom { predicate: name, args: vec![] });
        }
    }

    // Base: aux(i, 0) always true
    for row in &aux_atoms {
        rules.push(GroundRule { head: RuleHead::Normal(row[0]), body_pos: vec![], body_neg: vec![] });
    }

    // Forward rules (support):
    // aux(i, j) :- aux(i-1, j).           (skip element i)
    // aux(i, j) :- elem_i, aux(i-1, j-1). (include element i)
    //
    // Reverse constraints (completion — ensures aux[i][j] is true ONLY when supported):
    // :- aux(i,j), not aux(i-1,j), not elem_i.
    // :- aux(i,j), not aux(i-1,j), not aux(i-1,j-1).
    for i in 1..=n {
        for j in 1..=target.min(i) {
            // Forward: skip
            rules.push(GroundRule {
                head: RuleHead::Normal(aux_atoms[i][j]),
                body_pos: vec![aux_atoms[i - 1][j]],
                body_neg: vec![],
            });
            // Forward: include
            rules.push(GroundRule {
                head: RuleHead::Normal(aux_atoms[i][j]),
                body_pos: vec![ground_elements[i - 1], aux_atoms[i - 1][j - 1]],
                body_neg: vec![],
            });
            // Reverse: if aux[i][j] true, at least one support path must hold
            // :- aux[i][j], not aux[i-1][j], not elem[i-1].
            rules.push(GroundRule {
                head: RuleHead::Constraint,
                body_pos: vec![aux_atoms[i][j]],
                body_neg: vec![aux_atoms[i - 1][j], ground_elements[i - 1]],
            });
            // :- aux[i][j], not aux[i-1][j], not aux[i-1][j-1].
            rules.push(GroundRule {
                head: RuleHead::Constraint,
                body_pos: vec![aux_atoms[i][j]],
                body_neg: vec![aux_atoms[i - 1][j], aux_atoms[i - 1][j - 1]],
            });
        }
    }

    Some((rules, aux_atoms[n][target]))
}

/// Ground a #sum aggregate using knapsack-style DP encoding.
pub fn ground_sum(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    let weighted_elements = collect_weighted_elements(agg, bindings, facts, atom_table, const_map, 1);

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

    let n = weighted_elements.len();
    let max_sum: usize = weighted_elements.iter().map(|(w, _)| (*w).max(0) as usize).sum();
    let cap = target.min(max_sum);
    if cap == 0 || target > max_sum { return None; }

    let mut rules = Vec::new();
    let agg_id = atom_table.len();

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

    // DP transitions
    for i in 1..=n {
        let (wi, elem_id) = weighted_elements[i - 1];
        let wi = wi.max(0) as usize;
        for w in 1..=cap {
            rules.push(GroundRule {
                head: RuleHead::Normal(aux[i][w]),
                body_pos: vec![aux[i - 1][w]],
                body_neg: vec![],
            });
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

/// Ground a #min or #max aggregate.
///
/// Encoding:
/// - Existential (e.g. #min <= B, #max >= B): result :- elem_i for qualifying elems
/// - Universal (e.g. #min >= B, #max <= B): bad :- elem_i for violating; result :- not bad
/// - Equality: combination of both
///
/// ASP convention: #min of empty set = +∞, #max of empty set = -∞.
pub fn ground_minmax(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    let is_min = agg.function == AggFunction::Min;
    let weighted_elements = collect_weighted_elements(agg, bindings, facts, atom_table, const_map, 0);

    let (op, bound_term) = agg.upper.as_ref()?;
    let Value::Int(bound) = eval_term(bound_term, bindings, const_map)? else { return None; };

    let mut rules = Vec::new();
    let agg_id = atom_table.len();
    let result_name = interner.intern(&format!("__minmax_{agg_id}_result"));
    let result_id = atom_table.get_or_insert(GroundAtom { predicate: result_name, args: vec![] });

    // Partition elements into satisfying vs violating
    let (satisfying, violating): (Vec<AtomId>, Vec<AtomId>) = if is_min {
        match op {
            CompOp::Leq => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w <= bound).map(|(_, id)| *id).collect();
                (sat, vec![])
            }
            CompOp::Lt => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w < bound).map(|(_, id)| *id).collect();
                (sat, vec![])
            }
            CompOp::Geq => {
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w < bound).map(|(_, id)| *id).collect();
                (vec![], viol)
            }
            CompOp::Gt => {
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w <= bound).map(|(_, id)| *id).collect();
                (vec![], viol)
            }
            CompOp::Eq => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w == bound).map(|(_, id)| *id).collect();
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w < bound).map(|(_, id)| *id).collect();
                (sat, viol)
            }
            CompOp::Neq => return None,
        }
    } else {
        match op {
            CompOp::Geq => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w >= bound).map(|(_, id)| *id).collect();
                (sat, vec![])
            }
            CompOp::Gt => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w > bound).map(|(_, id)| *id).collect();
                (sat, vec![])
            }
            CompOp::Leq => {
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w > bound).map(|(_, id)| *id).collect();
                (vec![], viol)
            }
            CompOp::Lt => {
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w >= bound).map(|(_, id)| *id).collect();
                (vec![], viol)
            }
            CompOp::Eq => {
                let sat: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w == bound).map(|(_, id)| *id).collect();
                let viol: Vec<_> = weighted_elements.iter().filter(|(w, _)| *w > bound).map(|(_, id)| *id).collect();
                (sat, viol)
            }
            CompOp::Neq => return None,
        }
    };

    if !violating.is_empty() {
        // Universal pattern: result holds unless some violating element is true
        let bad_name = interner.intern(&format!("__minmax_{agg_id}_bad"));
        let bad_id = atom_table.get_or_insert(GroundAtom { predicate: bad_name, args: vec![] });
        for &elem_id in &violating {
            rules.push(GroundRule {
                head: RuleHead::Normal(bad_id),
                body_pos: vec![elem_id],
                body_neg: vec![],
            });
        }
        if satisfying.is_empty() {
            // Pure universal: result :- not bad.
            rules.push(GroundRule {
                head: RuleHead::Normal(result_id),
                body_pos: vec![],
                body_neg: vec![bad_id],
            });
        } else {
            // Mixed (equality): need both has_match AND not bad
            let has_name = interner.intern(&format!("__minmax_{agg_id}_has"));
            let has_id = atom_table.get_or_insert(GroundAtom { predicate: has_name, args: vec![] });
            for &elem_id in &satisfying {
                rules.push(GroundRule {
                    head: RuleHead::Normal(has_id),
                    body_pos: vec![elem_id],
                    body_neg: vec![],
                });
            }
            rules.push(GroundRule {
                head: RuleHead::Normal(result_id),
                body_pos: vec![has_id],
                body_neg: vec![bad_id],
            });
        }
    } else if !satisfying.is_empty() {
        // Pure existential: result :- satisfying_elem_i.
        for &elem_id in &satisfying {
            rules.push(GroundRule {
                head: RuleHead::Normal(result_id),
                body_pos: vec![elem_id],
                body_neg: vec![],
            });
        }
    } else {
        return None;
    }

    Some((rules, result_id))
}

/// Ground a single-bound aggregate (upper only).
fn ground_single_bound(
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
        AggFunction::Min | AggFunction::Max => ground_minmax(agg, bindings, facts, atom_table, interner, const_map),
    }
}

/// Dispatch aggregate grounding. Handles both single-bounded and double-bounded
/// aggregates. For double-bounded (`L op #agg{...} op U`), grounds each bound
/// separately and combines with conjunction: `result :- lower_ok, upper_ok.`
pub fn ground_aggregate(
    agg: &Aggregate,
    bindings: &Bindings,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    interner: &mut Interner,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(Vec<GroundRule>, AtomId)> {
    match (&agg.lower, &agg.upper) {
        (None, Some(_)) => ground_single_bound(agg, bindings, facts, atom_table, interner, const_map),
        (Some(_), None) => {
            // Lower only: swap lower to upper position for grounding
            let swapped = Aggregate {
                function: agg.function,
                elements: agg.elements.clone(),
                lower: None,
                upper: agg.lower.clone(),
            };
            ground_single_bound(&swapped, bindings, facts, atom_table, interner, const_map)
        }
        (Some(_), Some(_)) => {
            // Double-bounded: ground each bound separately, combine
            let lower_only = Aggregate {
                function: agg.function,
                elements: agg.elements.clone(),
                lower: None,
                upper: agg.lower.clone(),
            };
            let upper_only = Aggregate {
                function: agg.function,
                elements: agg.elements.clone(),
                lower: None,
                upper: agg.upper.clone(),
            };
            let (mut lo_rules, lo_id) = ground_single_bound(&lower_only, bindings, facts, atom_table, interner, const_map)?;
            let (hi_rules, hi_id) = ground_single_bound(&upper_only, bindings, facts, atom_table, interner, const_map)?;
            lo_rules.extend(hi_rules);
            // Combined result: both bounds must hold
            let agg_id = atom_table.len();
            let name = interner.intern(&format!("__agg_both_{agg_id}"));
            let result_id = atom_table.get_or_insert(GroundAtom { predicate: name, args: vec![] });
            lo_rules.push(GroundRule {
                head: RuleHead::Normal(result_id),
                body_pos: vec![lo_id, hi_id],
                body_neg: vec![],
            });
            Some((lo_rules, result_id))
        }
        (None, None) => None,
    }
}
