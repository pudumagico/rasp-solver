use std::collections::{HashMap, HashSet};

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{self, BinOp, BodyAtom, CompOp, Literal, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::aggregate;

/// Vec-backed bindings: O(1) lookup/insert/remove indexed by SymbolId.0.
#[derive(Debug)]
pub struct Bindings {
    slots: Vec<Option<Value>>,
}

impl Default for Bindings {
    fn default() -> Self { Self { slots: vec![None; 256] } }
}

impl Bindings {
    pub fn new() -> Self { Self::default() }
    pub fn get(&self, k: &SymbolId) -> Option<&Value> { self.slots.get(k.0 as usize)?.as_ref() }
    pub fn insert(&mut self, k: SymbolId, v: Value) {
        let i = k.0 as usize;
        if i >= self.slots.len() { self.slots.resize(i + 1, None); }
        self.slots[i] = Some(v);
    }
    pub fn remove(&mut self, k: &SymbolId) {
        if let Some(slot) = self.slots.get_mut(k.0 as usize) { *slot = None; }
    }
}

impl Clone for Bindings {
    fn clone(&self) -> Self { Self { slots: self.slots.clone() } }
}

pub type FactStore = HashMap<SymbolId, Vec<Vec<Value>>>;

/// Per-argument index: predicate -> [arg_position -> {value -> [tuple indices]}]
pub type ArgIndex = HashMap<SymbolId, Vec<HashMap<Value, Vec<usize>>>>;

pub fn build_arg_index(store: &FactStore) -> ArgIndex {
    let mut idx = ArgIndex::new();
    for (&pred, tuples) in store {
        let arity = tuples.first().map_or(0, |t| t.len());
        let mut per_arg: Vec<HashMap<Value, Vec<usize>>> = vec![HashMap::new(); arity];
        for (ti, tuple) in tuples.iter().enumerate() {
            if tuple.len() != arity { continue; }
            for (ai, val) in tuple.iter().enumerate() {
                per_arg[ai].entry(val.clone()).or_default().push(ti);
            }
        }
        idx.insert(pred, per_arg);
    }
    idx
}

/// Derived-key expression: computes a hash-join key from tuple arguments.
#[derive(Debug, Clone, Copy)]
pub enum DerivedKeyExpr {
    /// args[a] - args[b]
    ArgDiff(usize, usize),
    /// args[a] + args[b]
    ArgSum(usize, usize),
}

impl DerivedKeyExpr {
    fn eval_tuple(&self, tuple: &[Value]) -> Option<i64> {
        match *self {
            Self::ArgDiff(a, b) => match (&tuple[a], &tuple[b]) {
                (Value::Int(x), Value::Int(y)) => Some(x - y),
                _ => None,
            },
            Self::ArgSum(a, b) => match (&tuple[a], &tuple[b]) {
                (Value::Int(x), Value::Int(y)) => Some(x + y),
                _ => None,
            },
        }
    }
}

/// A derived-key join for a specific body literal index.
pub struct DerivedJoin {
    /// Which body literal index this join applies to
    pub body_idx: usize,
    /// The key expression to evaluate on already-bound variables (first atom's vars)
    pub bound_key_expr: Term,
    /// Hash index: derived key value -> tuple indices for the second atom's predicate
    pub index: HashMap<i64, Vec<usize>>,
}

/// Map from body literal index -> DerivedJoin
pub type DerivedJoinMap = HashMap<usize, DerivedJoin>;

/// Build a derived-key index for a predicate from a FactStore.
pub fn build_derived_index(
    store: &FactStore,
    pred: SymbolId,
    key_expr: DerivedKeyExpr,
) -> HashMap<i64, Vec<usize>> {
    let mut index = HashMap::new();
    if let Some(tuples) = store.get(&pred) {
        for (ti, tuple) in tuples.iter().enumerate() {
            if let Some(key) = key_expr.eval_tuple(tuple) {
                index.entry(key).or_insert_with(Vec::new).push(ti);
            }
        }
    }
    index
}

/// Context needed for grounding aggregates inside rule/constraint bodies.
pub struct AggContext<'a> {
    pub facts: &'a FactStore,
    pub interner: &'a mut Interner,
    pub const_map: &'a HashMap<SymbolId, Value>,
}

/// Instantiate a rule (possibly disjunctive) using `domain` for positive matching.
pub fn instantiate_rule_with_domain(
    heads: &[ast::Atom],
    body: &[Literal],
    facts: &FactStore,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    agg_ctx: Option<&mut AggContext<'_>>,
) -> Vec<GroundRule> {
    let idx = build_arg_index(domain);
    instantiate_rule_with_index(heads, body, facts, domain, atom_table, const_map, agg_ctx, &idx)
}

#[allow(clippy::too_many_arguments)]
pub fn instantiate_rule_with_index(
    heads: &[ast::Atom],
    body: &[Literal],
    facts: &FactStore,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    agg_ctx: Option<&mut AggContext<'_>>,
    arg_idx: &ArgIndex,
) -> Vec<GroundRule> {
    let mut results = Vec::new();
    let mut bindings = Bindings::new();
    let mut trail = Vec::new();
    let has_cond = body.iter().any(|l| matches!(l,
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..))));
    let no_dj = DerivedJoinMap::new();
    enumerate_body(body, 0, &mut bindings, domain, facts, const_map, &mut trail, arg_idx, &no_dj, &mut |b| {
        let ground_heads: Vec<AtomId> = heads.iter()
            .filter_map(|h| ground_atom(h, b, const_map))
            .map(|ga| atom_table.get_or_insert(ga))
            .collect();
        if ground_heads.is_empty() { return; }
        let (body_pos, body_neg) = ground_body(body, b, atom_table, const_map);
        let head = if ground_heads.len() == 1 {
            RuleHead::Normal(ground_heads[0])
        } else {
            RuleHead::Disjunction(ground_heads)
        };
        results.push(GroundRule { head, body_pos, body_neg });
    });
    if has_cond {
        ground_body_cond_literals(body, &bindings, domain, atom_table, const_map, &mut results);
    }
    if let Some(ctx) = agg_ctx {
        ground_body_aggregates(body, &bindings, domain, atom_table, ctx, &mut results);
    }
    results
}

/// Instantiate a constraint. Uses `domain` for positive body matching (includes
/// choice atoms) and `facts` for NAF matching (only definite facts).
pub fn instantiate_constraint(
    body: &[Literal],
    facts: &FactStore,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    agg_ctx: Option<&mut AggContext<'_>>,
) -> Vec<GroundRule> {
    let idx = build_arg_index(domain);
    instantiate_constraint_with_index(body, facts, domain, atom_table, const_map, agg_ctx, &idx)
}

pub fn instantiate_constraint_with_index(
    body: &[Literal],
    facts: &FactStore,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    agg_ctx: Option<&mut AggContext<'_>>,
    arg_idx: &ArgIndex,
) -> Vec<GroundRule> {
    let dj = detect_derived_joins(body, domain);
    instantiate_constraint_impl(body, facts, domain, atom_table, const_map, agg_ctx, arg_idx, &dj)
}

#[allow(clippy::too_many_arguments)]
fn instantiate_constraint_impl(
    body: &[Literal],
    facts: &FactStore,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    agg_ctx: Option<&mut AggContext<'_>>,
    arg_idx: &ArgIndex,
    derived_joins: &DerivedJoinMap,
) -> Vec<GroundRule> {
    let mut results = Vec::new();
    let mut bindings = Bindings::new();
    let mut trail = Vec::new();
    let has_cond = body.iter().any(|l| matches!(l,
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..))));
    enumerate_body(body, 0, &mut bindings, domain, facts, const_map, &mut trail, arg_idx, derived_joins, &mut |b| {
        let (body_pos, body_neg) = ground_body(body, b, atom_table, const_map);
        results.push(GroundRule { head: RuleHead::Constraint, body_pos, body_neg });
    });
    if has_cond {
        ground_body_cond_literals(body, &Bindings::new(), domain, atom_table, const_map, &mut results);
    }
    if let Some(ctx) = agg_ctx {
        ground_body_aggregates(body, &Bindings::new(), domain, atom_table, ctx, &mut results);
    }
    results
}

/// Instantiate a choice rule. Expands conditional elements by iterating
/// over all matching condition bindings.
pub fn instantiate_choice(
    choice: &ast::ChoiceRule,
    facts: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
) -> Vec<GroundRule> {
    let mut results = Vec::new();
    let mut bindings = Bindings::new();
    let mut trail = Vec::new();
    let arg_idx = build_arg_index(facts);
    let no_dj = DerivedJoinMap::new();
    enumerate_body(&choice.body, 0, &mut bindings, facts, facts, const_map, &mut trail, &arg_idx, &no_dj, &mut |b| {
        let mut head_atoms = Vec::new();
        for elem in &choice.elements {
            if elem.condition.is_empty() {
                // No condition — ground the atom directly
                if let Some(ga) = ground_atom(&elem.atom, b, const_map) {
                    head_atoms.push(atom_table.get_or_insert(ga));
                }
            } else {
                expand_choice_condition(
                    &elem.atom, &elem.condition, b, facts, const_map, atom_table, &mut head_atoms, &arg_idx,
                );
            }
        }
        if !head_atoms.is_empty() {
            let (body_pos, body_neg) = ground_body(&choice.body, b, atom_table, const_map);
            results.push(GroundRule { head: RuleHead::Choice(head_atoms), body_pos, body_neg });
        }
    });
    results
}

/// Public wrapper for enumerate_body.
pub fn enumerate_body_public(
    body: &[Literal],
    idx: usize,
    bindings: &Bindings,
    pos_domain: &FactStore,
    naf_facts: &FactStore,
    const_map: &HashMap<SymbolId, Value>,
    callback: &mut impl FnMut(&Bindings),
) {
    let mut b = bindings.clone();
    let mut trail = Vec::new();
    let arg_idx = build_arg_index(pos_domain);
    let no_dj = DerivedJoinMap::new();
    enumerate_body(body, idx, &mut b, pos_domain, naf_facts, const_map, &mut trail, &arg_idx, &no_dj, callback);
}

/// For a single-variable domain atom, collect values that are forbidden by `!=`
/// comparisons and out-of-range by `>`, `<`, `>=`, `<=` comparisons in the remaining body.
/// Returns None if no constraints apply (avoid allocating a HashSet).
fn collect_forbidden_values(
    body: &[Literal],
    current_idx: usize,
    var: SymbolId,
    bindings: &Bindings,
    const_map: &HashMap<SymbolId, Value>,
    domain_values: &[Vec<Value>],
) -> Option<HashSet<Value>> {
    let mut forbidden = HashSet::new();
    // Track range bounds: var must be > lower_excl, < upper_excl, >= lower_incl, <= upper_incl
    let mut lower_excl: Option<i64> = None; // var > lower_excl
    let mut upper_excl: Option<i64> = None; // var < upper_excl

    // Scan remaining body for comparisons involving `var`
    for lit in &body[current_idx + 1..] {
        let (cmp, negated) = match lit {
            Literal::Pos(BodyAtom::Comparison(c)) => (c, false),
            Literal::Neg(BodyAtom::Comparison(c)) => (c, true),
            _ => continue,
        };
        // Identify which side is our variable and which is the "other" term
        let is_var = |t: &Term| matches!(t, Term::Variable(v) if *v == var);
        // var OP other  or  other OP var
        let (effective_op, other_val) = if is_var(&cmp.left) {
            if let Some(v) = eval_term(&cmp.right, bindings, const_map) {
                (if negated { negate_comp(cmp.op) } else { cmp.op }, v)
            } else { continue; }
        } else if is_var(&cmp.right) {
            if let Some(v) = eval_term(&cmp.left, bindings, const_map) {
                // Flip: other OP var  →  var (flip OP) other
                (if negated { negate_comp(flip_comp(cmp.op)) } else { flip_comp(cmp.op) }, v)
            } else { continue; }
        } else { continue; };

        match (&effective_op, &other_val) {
            (CompOp::Neq, val) => { forbidden.insert(val.clone()); }
            (CompOp::Gt, Value::Int(n)) => {
                // var > n: tighten lower bound
                lower_excl = Some(lower_excl.map_or(*n, |prev| prev.max(*n)));
            }
            (CompOp::Geq, Value::Int(n)) => {
                // var >= n  ≡  var > (n-1)
                let bound = *n - 1;
                lower_excl = Some(lower_excl.map_or(bound, |prev| prev.max(bound)));
            }
            (CompOp::Lt, Value::Int(n)) => {
                // var < n: tighten upper bound
                upper_excl = Some(upper_excl.map_or(*n, |prev| prev.min(*n)));
            }
            (CompOp::Leq, Value::Int(n)) => {
                // var <= n  ≡  var < (n+1)
                let bound = *n + 1;
                upper_excl = Some(upper_excl.map_or(bound, |prev| prev.min(bound)));
            }
            _ => {}
        }
    }

    // Convert range bounds to forbidden values by scanning the domain
    if lower_excl.is_some() || upper_excl.is_some() {
        for tuple in domain_values {
            if tuple.len() == 1
                && let Value::Int(v) = &tuple[0]
                    && (lower_excl.is_some_and(|lo| *v <= lo)
                        || upper_excl.is_some_and(|hi| *v >= hi)) {
                        forbidden.insert(tuple[0].clone());
                    }
        }
    }

    if forbidden.is_empty() { None } else { Some(forbidden) }
}

/// Flip comparison direction: `a OP b` → `b (flip OP) a`
fn flip_comp(op: CompOp) -> CompOp {
    match op {
        CompOp::Lt => CompOp::Gt,
        CompOp::Gt => CompOp::Lt,
        CompOp::Leq => CompOp::Geq,
        CompOp::Geq => CompOp::Leq,
        other => other, // Eq, Neq are symmetric
    }
}

/// Negate a comparison: `not (a OP b)` → `a (neg OP) b`
fn negate_comp(op: CompOp) -> CompOp {
    match op {
        CompOp::Eq => CompOp::Neq,
        CompOp::Neq => CompOp::Eq,
        CompOp::Lt => CompOp::Geq,
        CompOp::Geq => CompOp::Lt,
        CompOp::Gt => CompOp::Leq,
        CompOp::Leq => CompOp::Gt,
    }
}

/// Check if a tuple value is forbidden by the pre-computed set.
/// Only applies to single-element tuples (arity-1 domain atoms).
fn is_forbidden(tuple: &[Value], forbidden: &Option<HashSet<Value>>) -> bool {
    if let Some(set) = forbidden {
        tuple.len() == 1 && set.contains(&tuple[0])
    } else {
        false
    }
}

#[allow(clippy::too_many_arguments)]
fn enumerate_body(
    body: &[Literal],
    idx: usize,
    bindings: &mut Bindings,
    pos_domain: &FactStore,
    naf_facts: &FactStore,
    const_map: &HashMap<SymbolId, Value>,
    trail: &mut Vec<SymbolId>,
    arg_idx: &ArgIndex,
    derived_joins: &DerivedJoinMap,
    callback: &mut impl FnMut(&Bindings),
) {
    if idx >= body.len() {
        callback(bindings);
        return;
    }
    match &body[idx] {
        Literal::Pos(BodyAtom::Atom(atom)) => {
            let Some(tuples) = pos_domain.get(&atom.predicate) else { return; };

            // Pre-compute forbidden values for single-variable domain atoms
            // (forward checking for != / > / < constraints)
            let forbidden = if atom.args.len() == 1 {
                if let Term::Variable(v) = &atom.args[0] {
                    if bindings.get(v).is_none() {
                        collect_forbidden_values(body, idx, *v, bindings, const_map, tuples)
                    } else { None }
                } else { None }
            } else { None };
            // When forbidden values are active, we can skip the expensive eager
            // comparison check if the only remaining comparisons are !=/>/</>=/<=
            // (all handled by forbidden set). Only need eager check for = solving.
            let skip_eager = forbidden.is_some() && !body[idx + 1..].iter().any(|l| {
                matches!(l, Literal::Pos(BodyAtom::Comparison(c)) if c.op == CompOp::Eq)
            });

            // Check for derived-key join: use hash index instead of full scan
            if let Some(dj) = derived_joins.get(&idx)
                && let Some(Value::Int(key)) = eval_term(&dj.bound_key_expr, bindings, const_map) {
                    if let Some(indices) = dj.index.get(&key) {
                        for &ti in indices {
                            let tuple = &tuples[ti];
                            if is_forbidden(tuple, &forbidden) { continue; }
                            let saved = trail.len();
                            if unify_args_trail(&atom.args, tuple, bindings, const_map, trail)
                                && (skip_eager || check_eager_comparisons(body, idx + 1, bindings, const_map, trail)) {
                                enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                            }
                            undo_trail(bindings, trail, saved);
                        }
                    }
                    return;
                }

            // Find the most selective argument index
            let best = arg_idx.get(&atom.predicate).and_then(|per_arg| {
                let mut best: Option<&[usize]> = None;
                for (pos, arg) in atom.args.iter().enumerate() {
                    if pos < per_arg.len()
                        && let Some(val) = eval_term(arg, bindings, const_map) {
                            if let Some(indices) = per_arg[pos].get(&val) {
                                if best.is_none() || indices.len() < best.unwrap().len() {
                                    best = Some(indices.as_slice());
                                }
                            } else {
                                return Some(&[] as &[usize]);
                            }
                        }
                }
                best
            });
            if let Some(indices) = best {
                for &ti in indices {
                    let tuple = &tuples[ti];
                    if is_forbidden(tuple, &forbidden) { continue; }
                    let saved = trail.len();
                    if unify_args_trail(&atom.args, tuple, bindings, const_map, trail)
                        && (skip_eager || check_eager_comparisons(body, idx + 1, bindings, const_map, trail)) {
                        enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                    }
                    undo_trail(bindings, trail, saved);
                }
            } else {
                for tuple in tuples {
                    if tuple.len() != atom.args.len() { continue; }
                    if is_forbidden(tuple, &forbidden) { continue; }
                    let saved = trail.len();
                    if unify_args_trail(&atom.args, tuple, bindings, const_map, trail)
                        && (skip_eager || check_eager_comparisons(body, idx + 1, bindings, const_map, trail)) {
                        enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                    }
                    undo_trail(bindings, trail, saved);
                }
            }
        }
        Literal::Neg(BodyAtom::Atom(atom)) => {
            let matches = if let Some(tuples) = naf_facts.get(&atom.predicate) {
                tuples.iter().any(|tuple| {
                    if tuple.len() != atom.args.len() { return false; }
                    let saved = trail.len();
                    let ok = unify_args_trail(&atom.args, tuple, bindings, const_map, trail);
                    undo_trail(bindings, trail, saved);
                    ok
                })
            } else {
                false
            };
            if !matches {
                enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
            }
        }
        Literal::Pos(BodyAtom::Comparison(cmp)) | Literal::Neg(BodyAtom::Comparison(cmp)) => {
            let negated = matches!(&body[idx], Literal::Neg(_));
            // Try to solve for an unbound variable in positive equalities
            if !negated && cmp.op == CompOp::Eq
                && let Some((var, val)) = try_solve_equality(cmp, bindings, const_map) {
                    let saved = trail.len();
                    trail.push(var);
                    bindings.insert(var, val);
                    enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                    undo_trail(bindings, trail, saved);
                    return;
                }
            if let (Some(lv), Some(rv)) = (eval_term(&cmp.left, bindings, const_map), eval_term(&cmp.right, bindings, const_map)) {
                let holds = eval_comp(cmp.op, &lv, &rv);
                let pass = if negated { !holds } else { holds };
                if pass {
                    enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                }
            }
        }
        Literal::Pos(BodyAtom::Aggregate(_)) | Literal::Neg(BodyAtom::Aggregate(_)) => {
            enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
        }
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..)) => {
            enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
        }
    }
}

/// Unify with trail: records newly bound variables for undo.
fn unify_args_trail(
    args: &[Term],
    tuple: &[Value],
    bindings: &mut Bindings,
    const_map: &HashMap<SymbolId, Value>,
    trail: &mut Vec<SymbolId>,
) -> bool {
    for (arg, val) in args.iter().zip(tuple.iter()) {
        match arg {
            Term::Variable(v) => {
                if let Some(existing) = bindings.get(v) {
                    if existing != val { return false; }
                } else {
                    trail.push(*v);
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

/// Try to solve `cmp` (an equality) for a single unbound variable.
/// Handles: V = expr, expr = V, V +/- expr = val, expr +/- V = val, and reverses.
fn try_solve_equality(
    cmp: &ast::Comparison,
    bindings: &Bindings,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(SymbolId, Value)> {
    // Direct: Variable = evaluated_expr  or  evaluated_expr = Variable
    if let Term::Variable(v) = &cmp.left
        && bindings.get(v).is_none() {
            return Some((*v, eval_term(&cmp.right, bindings, const_map)?));
        }
    if let Term::Variable(v) = &cmp.right
        && bindings.get(v).is_none() {
            return Some((*v, eval_term(&cmp.left, bindings, const_map)?));
        }
    // BinOp on one side with an unbound variable, other side evaluable
    try_solve_binop_side(&cmp.left, &cmp.right, bindings, const_map)
        .or_else(|| try_solve_binop_side(&cmp.right, &cmp.left, bindings, const_map))
}

/// Solve `binop_side = other_side` where binop_side is `V op expr` or `expr op V`.
fn try_solve_binop_side(
    binop_side: &Term,
    other_side: &Term,
    bindings: &Bindings,
    const_map: &HashMap<SymbolId, Value>,
) -> Option<(SymbolId, Value)> {
    let Term::BinOp(op, l, r) = binop_side else { return None; };
    let Value::Int(rhs) = eval_term(other_side, bindings, const_map)? else { return None; };
    // Case: V op expr = rhs  (left is unbound variable)
    if let Term::Variable(v) = l.as_ref()
        && bindings.get(v).is_none() {
            let Value::Int(e) = eval_term(r, bindings, const_map)? else { return None; };
            // V + e = rhs => V = rhs - e;  V - e = rhs => V = rhs + e
            let solved = match op {
                BinOp::Add => rhs.checked_sub(e)?,
                BinOp::Sub => rhs.checked_add(e)?,
                _ => return None,
            };
            return Some((*v, Value::Int(solved)));
        }
    // Case: expr op V = rhs  (right is unbound variable)
    if let Term::Variable(v) = r.as_ref()
        && bindings.get(v).is_none() {
            let Value::Int(e) = eval_term(l, bindings, const_map)? else { return None; };
            // e + V = rhs => V = rhs - e;  e - V = rhs => V = e - rhs
            let solved = match op {
                BinOp::Add => rhs.checked_sub(e)?,
                BinOp::Sub => e.checked_sub(rhs)?,
                _ => return None,
            };
            return Some((*v, Value::Int(solved)));
        }
    None
}

/// Eagerly evaluate remaining comparisons and solve equalities with one free variable.
/// Also checks positive atom lookups where all args are ground (early pruning).
/// Binds solved variables (pushed to trail) so later literals can verify them.
/// Returns false if any fully-evaluable comparison or atom lookup fails.
fn check_eager_comparisons(
    body: &[Literal],
    from_idx: usize,
    bindings: &mut Bindings,
    const_map: &HashMap<SymbolId, Value>,
    trail: &mut Vec<SymbolId>,
) -> bool {
    let mut solved = false;
    for lit in &body[from_idx..] {
        let (cmp, negated) = match lit {
            Literal::Pos(BodyAtom::Comparison(c)) => (c, false),
            Literal::Neg(BodyAtom::Comparison(c)) => (c, true),
            _ => continue,
        };
        // Fast path: skip comparisons with clearly unbound variables
        // (avoids expensive eval_term on expressions with free vars)
        if has_unbound_var(&cmp.left, bindings) || has_unbound_var(&cmp.right, bindings) {
            // But still try to solve equalities with one free variable
            if !negated && cmp.op == CompOp::Eq
                && let Some((var, val)) = try_solve_equality(cmp, bindings, const_map) {
                    trail.push(var);
                    bindings.insert(var, val);
                    solved = true;
                }
            continue;
        }
        let lv = eval_term(&cmp.left, bindings, const_map);
        let rv = eval_term(&cmp.right, bindings, const_map);
        if let (Some(l), Some(r)) = (lv, rv)
            && negated == eval_comp(cmp.op, &l, &r) { return false; }
    }
    if !solved { return true; }
    // Second pass: recheck comparisons that might now be evaluable after solving
    for lit in &body[from_idx..] {
        let (cmp, negated) = match lit {
            Literal::Pos(BodyAtom::Comparison(c)) => (c, false),
            Literal::Neg(BodyAtom::Comparison(c)) => (c, true),
            _ => continue,
        };
        if !negated && cmp.op == CompOp::Eq { continue; }
        if has_unbound_var(&cmp.left, bindings) || has_unbound_var(&cmp.right, bindings) { continue; }
        if let (Some(l), Some(r)) = (eval_term(&cmp.left, bindings, const_map), eval_term(&cmp.right, bindings, const_map))
            && negated == eval_comp(cmp.op, &l, &r) { return false; }
    }
    true
}

/// Quick check if a term contains a variable not yet bound. Avoids full eval_term.
fn has_unbound_var(term: &Term, bindings: &Bindings) -> bool {
    match term {
        Term::Variable(v) => bindings.get(v).is_none(),
        Term::BinOp(_, l, r) => has_unbound_var(l, bindings) || has_unbound_var(r, bindings),
        Term::UnaryMinus(t) | Term::Abs(t) => has_unbound_var(t, bindings),
        Term::Function(_, args) => args.iter().any(|a| has_unbound_var(a, bindings)),
        Term::Integer(_) | Term::Symbolic(_) | Term::StringConst(_) | Term::Anonymous => false,
        Term::Range(a, b) => has_unbound_var(a, bindings) || has_unbound_var(b, bindings),
        Term::Pool(ts) => ts.iter().any(|t| has_unbound_var(t, bindings)),
    }
}



fn undo_trail(bindings: &mut Bindings, trail: &mut Vec<SymbolId>, saved: usize) {
    while trail.len() > saved {
        let var = trail.pop().unwrap();
        bindings.remove(&var);
    }
}

pub fn eval_term(term: &Term, bindings: &Bindings, const_map: &HashMap<SymbolId, Value>) -> Option<Value> {
    match term {
        Term::Integer(n) => Some(Value::Int(*n)),
        Term::Variable(v) => bindings.get(v).cloned(),
        Term::Symbolic(s) => Some(const_map.get(s).cloned().unwrap_or(Value::Sym(*s))),
        Term::StringConst(s) => Some(Value::Sym(*s)),
        Term::BinOp(op, l, r) => {
            let Value::Int(lv) = eval_term(l, bindings, const_map)? else { return None; };
            let Value::Int(rv) = eval_term(r, bindings, const_map)? else { return None; };
            let result = match op {
                BinOp::Add => lv.checked_add(rv)?,
                BinOp::Sub => lv.checked_sub(rv)?,
                BinOp::Mul => lv.checked_mul(rv)?,
                BinOp::Div => { if rv == 0 { return None; } lv.checked_div(rv)? }
                BinOp::Mod => { if rv == 0 { return None; } lv.checked_rem(rv)? }
                BinOp::Pow => { if rv < 0 { return None; } lv.checked_pow(rv as u32)? }
            };
            Some(Value::Int(result))
        }
        Term::UnaryMinus(inner) => {
            let Value::Int(v) = eval_term(inner, bindings, const_map)? else { return None; };
            Some(Value::Int(-v))
        }
        Term::Abs(inner) => {
            let Value::Int(v) = eval_term(inner, bindings, const_map)? else { return None; };
            Some(Value::Int(v.abs()))
        }
        Term::Function(name, args) => {
            if args.is_empty() {
                Some(Value::Sym(*name))
            } else {
                None
            }
        }
        Term::Pool(..) | Term::Range(..) | Term::Anonymous => None,
    }
}

fn eval_comp(op: CompOp, left: &Value, right: &Value) -> bool {
    match op {
        CompOp::Eq => left == right,
        CompOp::Neq => left != right,
        CompOp::Lt => left < right,
        CompOp::Gt => left > right,
        CompOp::Leq => left <= right,
        CompOp::Geq => left >= right,
    }
}

fn ground_atom(atom: &ast::Atom, bindings: &Bindings, const_map: &HashMap<SymbolId, Value>) -> Option<GroundAtom> {
    let args: Option<Vec<Value>> = atom.args.iter().map(|t| eval_term(t, bindings, const_map)).collect();
    Some(GroundAtom { predicate: atom.predicate, args: args? })
}

/// Expand a choice element's condition by enumerating all matching bindings,
/// producing one head atom per valid binding.
#[allow(clippy::too_many_arguments)]
fn expand_choice_condition(
    atom: &ast::Atom,
    condition: &[Literal],
    base_bindings: &Bindings,
    facts: &FactStore,
    const_map: &HashMap<SymbolId, Value>,
    atom_table: &mut AtomTable,
    head_atoms: &mut Vec<AtomId>,
    arg_idx: &ArgIndex,
) {
    let mut b = base_bindings.clone();
    let mut trail = Vec::new();
    let no_dj = DerivedJoinMap::new();
    enumerate_body(condition, 0, &mut b, facts, facts, const_map, &mut trail, arg_idx, &no_dj, &mut |b| {
        if let Some(ga) = ground_atom(atom, b, const_map) {
            let id = atom_table.get_or_insert(ga);
            if !head_atoms.contains(&id) {
                head_atoms.push(id);
            }
        }
    });
}

fn ground_body(
    body: &[Literal],
    bindings: &Bindings,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
) -> (Vec<AtomId>, Vec<AtomId>) {
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    for lit in body {
        let (ba, is_neg) = match lit {
            Literal::Pos(ba) => (ba, false),
            Literal::Neg(ba) => (ba, true),
        };
        match ba {
            BodyAtom::Atom(a) => {
                if let Some(ga) = ground_atom(a, bindings, const_map) {
                    let id = atom_table.get_or_insert(ga);
                    if is_neg { neg.push(id); } else { pos.push(id); }
                }
            }
            BodyAtom::Aggregate(_) => {
                // Handled by ground_body_aggregates
            }
            BodyAtom::Comparison(_) => {}
            BodyAtom::CondLiteral(_, _) => {
                // Handled by ground_body_cond_literals
            }
        }
    }
    (pos, neg)
}

/// Expand conditional body literals (`p(X) : q(X)`) into conjunctions.
/// For each ground binding from the condition domain, creates the grounded
/// atom (even if it doesn't exist yet) and adds it to parent rules' bodies.
fn ground_body_cond_literals(
    body: &[Literal],
    bindings: &Bindings,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    const_map: &HashMap<SymbolId, Value>,
    rules: &mut [GroundRule],
) {
    let parent_count = rules.len();
    for lit in body {
        let (ba, is_neg) = match lit {
            Literal::Pos(ba) => (ba, false),
            Literal::Neg(ba) => (ba, true),
        };
        if let BodyAtom::CondLiteral(atom, condition) = ba {
            // Enumerate condition domain to get bindings, then ground the atom.
            // Use get_or_insert to create atoms that don't exist yet (they'll
            // have no support and be forced false by Clark's completion).
            let mut cond_atoms = Vec::new();
            let mut cond_bindings_mut = bindings.clone();
            let mut cond_trail = Vec::new();
            let cond_arg_idx = build_arg_index(domain);
            let no_dj = DerivedJoinMap::new();
            enumerate_body(condition, 0, &mut cond_bindings_mut, domain, domain, const_map, &mut cond_trail, &cond_arg_idx, &no_dj, &mut |cond_bindings| {
                if let Some(ga) = ground_atom(atom, cond_bindings, const_map) {
                    let id = atom_table.get_or_insert(ga);
                    if !cond_atoms.contains(&id) {
                        cond_atoms.push(id);
                    }
                }
            });
            for rule in rules[..parent_count].iter_mut() {
                for &id in &cond_atoms {
                    if is_neg { rule.body_neg.push(id); } else { rule.body_pos.push(id); }
                }
            }
        }
    }
}

/// Ground all aggregates that appear in body literals. For each aggregate,
/// call `ground_aggregate` to produce auxiliary rules + result atom, then
/// patch the result atom into the body of the parent rules (not aux rules).
///
/// If a positive aggregate returns None (unsatisfiable), all parent rules
/// are removed (body can never be satisfied). If a negated aggregate returns
/// None, its negation is trivially true and the literal is omitted.
fn ground_body_aggregates(
    body: &[Literal],
    bindings: &Bindings,
    domain: &FactStore,
    atom_table: &mut AtomTable,
    ctx: &mut AggContext<'_>,
    rules: &mut Vec<GroundRule>,
) {
    let parent_count = rules.len();
    for lit in body {
        let (ba, is_neg) = match lit {
            Literal::Pos(ba) => (ba, false),
            Literal::Neg(ba) => (ba, true),
        };
        if let BodyAtom::Aggregate(agg) = ba {
            match aggregate::ground_aggregate(
                agg, bindings, domain, atom_table, ctx.interner, ctx.const_map,
            ) {
                Some((aux_rules, result_id)) => {
                    for rule in rules[..parent_count].iter_mut() {
                        if is_neg {
                            rule.body_neg.push(result_id);
                        } else {
                            rule.body_pos.push(result_id);
                        }
                    }
                    rules.extend(aux_rules);
                }
                None => {
                    if !is_neg {
                        // Positive aggregate that can never be true → remove all parent rules
                        rules.drain(..parent_count);
                    }
                    // Negated aggregate that can never be true → always true → no-op
                }
            }
        }
    }
}

/// Collect all variables from an AST term.
fn collect_term_vars(t: &Term, vars: &mut Vec<SymbolId>) {
    match t {
        Term::Variable(v) => vars.push(*v),
        Term::BinOp(_, l, r) => { collect_term_vars(l, vars); collect_term_vars(r, vars); }
        Term::UnaryMinus(inner) => collect_term_vars(inner, vars),
        Term::Function(_, args) => { for a in args { collect_term_vars(a, vars); } }
        _ => {}
    }
}

/// Detect self-join patterns connected by arithmetic equality and build derived-key indices.
///
/// Looks for patterns like: `pred(V1,V2), pred(V3,V4), expr_over_V1V2 = expr_over_V3V4`
/// where the two positive atoms share the same predicate and the equality connects
/// variables from the first atom to the second. Builds a hash index on the derived key.
fn detect_derived_joins(body: &[Literal], domain: &FactStore) -> DerivedJoinMap {
    let mut result = DerivedJoinMap::new();

    // Find all positive atom positions with their predicates and variable sets
    let mut pos_atoms: Vec<(usize, SymbolId, HashSet<SymbolId>)> = Vec::new();
    for (i, lit) in body.iter().enumerate() {
        if let Literal::Pos(BodyAtom::Atom(atom)) = lit {
            let mut vars = HashSet::new();
            for arg in &atom.args {
                if let Term::Variable(v) = arg { vars.insert(*v); }
            }
            pos_atoms.push((i, atom.predicate, vars));
        }
    }

    // Look for self-join pairs (same predicate, different body indices)
    for a in 0..pos_atoms.len() {
        for b in (a + 1)..pos_atoms.len() {
            let (_, pred_a, ref vars_a) = pos_atoms[a];
            let (idx_b, pred_b, ref vars_b) = pos_atoms[b];
            if pred_a != pred_b { continue; }
            // Variables must be disjoint (different variable names for the two atoms)
            if !vars_a.is_disjoint(vars_b) { continue; }

            // Find an equality comparison connecting vars from atom_a to atom_b
            for lit in body {
                let cmp = match lit {
                    Literal::Pos(BodyAtom::Comparison(c)) if c.op == CompOp::Eq => c,
                    _ => continue,
                };

                let mut left_vars = Vec::new();
                let mut right_vars = Vec::new();
                collect_term_vars(&cmp.left, &mut left_vars);
                collect_term_vars(&cmp.right, &mut right_vars);

                // Check: left uses only vars_a, right uses only vars_b (or vice versa)
                let left_from_a = left_vars.iter().all(|v| vars_a.contains(v)) && !left_vars.is_empty();
                let right_from_b = right_vars.iter().all(|v| vars_b.contains(v)) && !right_vars.is_empty();
                let left_from_b = left_vars.iter().all(|v| vars_b.contains(v)) && !left_vars.is_empty();
                let right_from_a = right_vars.iter().all(|v| vars_a.contains(v)) && !right_vars.is_empty();

                // Determine which side is bound (atom_a, processed first) and which is the key expr
                let (bound_expr, key_expr_for_b) = if left_from_a && right_from_b {
                    (&cmp.left, &cmp.right)
                } else if left_from_b && right_from_a {
                    (&cmp.right, &cmp.left)
                } else {
                    continue;
                };

                // Try to derive a DerivedKeyExpr from key_expr_for_b
                // Map variables to argument positions in atom_b
                let atom_b = match &body[idx_b] {
                    Literal::Pos(BodyAtom::Atom(a)) => a,
                    _ => continue,
                };
                if let Some(dk_expr) = term_to_derived_key(key_expr_for_b, &atom_b.args) {
                    let index = build_derived_index(domain, pred_b, dk_expr);
                    result.insert(idx_b, DerivedJoin {
                        body_idx: idx_b,
                        bound_key_expr: bound_expr.clone(),
                        index,
                    });
                    break; // one derived join per second atom is enough
                }
            }
        }
    }

    result
}

/// Try to convert a term like `V3 - V4` into a `DerivedKeyExpr` using argument positions.
/// `atom_args` are the arguments of the atom (e.g., `[V3, V4]` for `pred(V3, V4)`).
fn term_to_derived_key(term: &Term, atom_args: &[Term]) -> Option<DerivedKeyExpr> {
    // Map: variable -> argument position in the atom
    let var_pos = |v: SymbolId| -> Option<usize> {
        atom_args.iter().position(|a| matches!(a, Term::Variable(vv) if *vv == v))
    };
    match term {
        Term::BinOp(BinOp::Sub, l, r) => {
            let Term::Variable(lv) = l.as_ref() else { return None; };
            let Term::Variable(rv) = r.as_ref() else { return None; };
            Some(DerivedKeyExpr::ArgDiff(var_pos(*lv)?, var_pos(*rv)?))
        }
        Term::BinOp(BinOp::Add, l, r) => {
            let Term::Variable(lv) = l.as_ref() else { return None; };
            let Term::Variable(rv) = r.as_ref() else { return None; };
            Some(DerivedKeyExpr::ArgSum(var_pos(*lv)?, var_pos(*rv)?))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::parser;

    #[test]
    fn instantiate_simple_rule() {
        let mut interner = Interner::new();
        let prog = parser::parse("a(1). a(2). b(X) :- a(X).", &mut interner).unwrap();
        let mut atom_table = AtomTable::new();
        let mut facts = FactStore::new();
        let a_id = interner.intern("a");
        facts.insert(a_id, vec![vec![Value::Int(1)], vec![Value::Int(2)]]);

        let ast::Statement::Rule(rule) = &prog.statements[2] else { panic!() };
        let rules = instantiate_rule_with_domain(&rule.head, &rule.body, &facts, &facts, &mut atom_table, &HashMap::new(), None);
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn eval_arithmetic_term() {
        let mut bindings = Bindings::new();
        let x = SymbolId(0);
        bindings.insert(x, Value::Int(3));
        let term = Term::BinOp(BinOp::Add, Box::new(Term::Variable(x)), Box::new(Term::Integer(1)));
        assert_eq!(eval_term(&term, &bindings, &HashMap::new()), Some(Value::Int(4)));
    }

    #[test]
    fn solve_equality_nested_expr() {
        // Test: A*10+B = C  where A=9, B bound, C unbound
        // Parses as: BinOp(Add, BinOp(Mul, A, 10), B) = C
        // try_solve_equality should solve C = 9*10+5 = 95
        let mut interner = Interner::new();
        let prog = parser::parse("p :- A*10+B = C.", &mut interner).unwrap();
        let ast::Statement::Rule(rule) = &prog.statements[0] else { panic!() };
        let cmp = match &rule.body[0] {
            Literal::Pos(BodyAtom::Comparison(c)) => c,
            _ => panic!("expected comparison"),
        };
        let a = interner.intern("A");
        let b = interner.intern("B");
        let c = interner.intern("C");
        let mut bindings = Bindings::new();
        bindings.insert(a, Value::Int(9));
        bindings.insert(b, Value::Int(5));
        let result = try_solve_equality(cmp, &bindings, &HashMap::new());
        assert_eq!(result, Some((c, Value::Int(95))));
    }

    #[test]
    fn solve_sendmoremoney_equality() {
        // Test the SEND+MORE=MONEY equality: S*1000+E*100+N*10+D + M*1000+O*100+R*10+E = M*10000+O*1000+N*100+E*10+Y
        // With all vars bound except Y, try_solve_equality should compute Y
        let mut interner = Interner::new();
        let prog = parser::parse(
            "p :- S*1000+E*100+N*10+D + M*1000+O*100+R*10+E = M*10000+O*1000+N*100+E*10+Y.",
            &mut interner,
        ).unwrap();
        let ast::Statement::Rule(rule) = &prog.statements[0] else { panic!() };
        let cmp = match &rule.body[0] {
            Literal::Pos(BodyAtom::Comparison(c)) => c,
            _ => panic!("expected comparison"),
        };
        // SEND=9567, MORE=1085, MONEY=10652
        // S=9,E=5,N=6,D=7,M=1,O=0,R=8,Y=2
        let mut bindings = Bindings::new();
        for (name, val) in [("S",9),("E",5),("N",6),("D",7),("M",1),("O",0),("R",8)] {
            bindings.insert(interner.intern(name), Value::Int(val));
        }
        let y = interner.intern("Y");
        let result = try_solve_equality(cmp, &bindings, &HashMap::new());
        assert_eq!(result, Some((y, Value::Int(2))));
    }

    #[test]
    fn eager_check_solves_and_prunes() {
        // Test that check_eager_comparisons solves for Y and prunes bad combos
        let mut interner = Interner::new();
        let prog = parser::parse(
            "p :- X + Y = 10, X > 0.",
            &mut interner,
        ).unwrap();
        let ast::Statement::Rule(rule) = &prog.statements[0] else { panic!() };
        let x = interner.intern("X");
        let y = interner.intern("Y");

        // X=3, Y unbound. Eager check should solve Y=7 and pass X>0.
        let mut bindings = Bindings::new();
        bindings.insert(x, Value::Int(3));
        let mut trail = Vec::new();
        let result = check_eager_comparisons(&rule.body, 0, &mut bindings, &HashMap::new(), &mut trail);
        assert!(result);
        assert_eq!(bindings.get(&y), Some(&Value::Int(7)));
        assert_eq!(trail, vec![y]);

        // X=0, Y unbound. Eager check should solve Y=10 but then X>0 fails.
        let mut bindings2 = Bindings::new();
        bindings2.insert(x, Value::Int(0));
        let mut trail2 = Vec::new();
        let result2 = check_eager_comparisons(&rule.body, 0, &mut bindings2, &HashMap::new(), &mut trail2);
        assert!(!result2);
    }
}
