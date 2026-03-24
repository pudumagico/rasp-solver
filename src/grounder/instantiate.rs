use std::collections::HashMap;

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{self, BinOp, BodyAtom, CompOp, Literal, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::aggregate;

pub type Bindings = HashMap<SymbolId, Value>;
pub type FactStore = HashMap<SymbolId, Vec<Vec<Value>>>;

/// Per-argument index: predicate -> [arg_position -> {value -> [tuple indices]}]
pub type ArgIndex = HashMap<SymbolId, Vec<HashMap<Value, Vec<usize>>>>;

pub fn build_arg_index(store: &FactStore) -> ArgIndex {
    let mut idx = ArgIndex::new();
    for (&pred, tuples) in store {
        let arity = tuples.first().map_or(0, |t| t.len());
        let mut per_arg: Vec<HashMap<Value, Vec<usize>>> = vec![HashMap::new(); arity];
        for (ti, tuple) in tuples.iter().enumerate() {
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

            // Check for derived-key join: use hash index instead of full scan
            if let Some(dj) = derived_joins.get(&idx)
                && let Some(Value::Int(key)) = eval_term(&dj.bound_key_expr, bindings, const_map) {
                    if let Some(indices) = dj.index.get(&key) {
                        for &ti in indices {
                            let tuple = &tuples[ti];
                            let saved = trail.len();
                            if unify_args_trail(&atom.args, tuple, bindings, const_map, trail) {
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
                    let saved = trail.len();
                    if unify_args_trail(&atom.args, tuple, bindings, const_map, trail) {
                        enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, trail, arg_idx, derived_joins, callback);
                    }
                    undo_trail(bindings, trail, saved);
                }
            } else {
                for tuple in tuples {
                    if tuple.len() != atom.args.len() { continue; }
                    let saved = trail.len();
                    if unify_args_trail(&atom.args, tuple, bindings, const_map, trail) {
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
            };
            Some(Value::Int(result))
        }
        Term::UnaryMinus(inner) => {
            let Value::Int(v) = eval_term(inner, bindings, const_map)? else { return None; };
            Some(Value::Int(-v))
        }
        Term::Function(name, args) => {
            if args.is_empty() {
                Some(Value::Sym(*name))
            } else {
                None
            }
        }
        Term::Range(..) | Term::Anonymous => None,
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
    use std::collections::HashSet;

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
}
