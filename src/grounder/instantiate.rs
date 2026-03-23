use std::collections::HashMap;

use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{self, BinOp, BodyAtom, CompOp, Literal, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::aggregate;

pub type Bindings = HashMap<SymbolId, Value>;
pub type FactStore = HashMap<SymbolId, Vec<Vec<Value>>>;

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
    let mut results = Vec::new();
    let bindings = Bindings::new();
    let has_cond = body.iter().any(|l| matches!(l,
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..))));
    enumerate_body(body, 0, &bindings, domain, facts, const_map, &mut |b| {
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
    let mut results = Vec::new();
    let bindings = Bindings::new();
    let has_cond = body.iter().any(|l| matches!(l,
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..))));
    enumerate_body(body, 0, &bindings, domain, facts, const_map, &mut |b| {
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
    let bindings = Bindings::new();
    enumerate_body(&choice.body, 0, &bindings, facts, facts, const_map, &mut |b| {
        let mut head_atoms = Vec::new();
        for elem in &choice.elements {
            if elem.condition.is_empty() {
                // No condition — ground the atom directly
                if let Some(ga) = ground_atom(&elem.atom, b, const_map) {
                    head_atoms.push(atom_table.get_or_insert(ga));
                }
            } else {
                // Expand condition: enumerate all matching bindings
                expand_choice_condition(
                    &elem.atom, &elem.condition, b, facts, const_map, atom_table, &mut head_atoms,
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
    enumerate_body(body, idx, bindings, pos_domain, naf_facts, const_map, callback);
}

/// Recursively enumerate all valid variable bindings for the body.
/// `pos_domain`: used for positive body atom matching (may include choice atoms).
/// `naf_facts`: used for NAF checks (only definite facts).
fn enumerate_body(
    body: &[Literal],
    idx: usize,
    bindings: &Bindings,
    pos_domain: &FactStore,
    naf_facts: &FactStore,
    const_map: &HashMap<SymbolId, Value>,
    callback: &mut impl FnMut(&Bindings),
) {
    if idx >= body.len() {
        callback(bindings);
        return;
    }
    match &body[idx] {
        Literal::Pos(BodyAtom::Atom(atom)) => {
            let Some(tuples) = pos_domain.get(&atom.predicate) else { return; };
            // Optimization: if first arg is ground, skip non-matching tuples early
            let first_ground = atom.args.first().and_then(|t| eval_term(t, bindings, const_map));
            for tuple in tuples {
                if tuple.len() != atom.args.len() { continue; }
                // Fast filter: check first argument before full unification
                if let Some(ref fv) = first_ground
                    && let Some(tv) = tuple.first()
                    && fv != tv { continue; }
                let mut new_bindings = bindings.clone();
                if unify_args(&atom.args, tuple, &mut new_bindings, const_map) {
                    enumerate_body(body, idx + 1, &new_bindings, pos_domain, naf_facts, const_map, callback);
                }
            }
        }
        Literal::Neg(BodyAtom::Atom(atom)) => {
            // NAF: check against definite facts only (not choice atoms)
            let matches = if let Some(tuples) = naf_facts.get(&atom.predicate) {
                tuples.iter().any(|tuple| {
                    if tuple.len() != atom.args.len() { return false; }
                    let mut test_bindings = bindings.clone();
                    unify_args(&atom.args, tuple, &mut test_bindings, const_map)
                })
            } else {
                false
            };
            if !matches {
                enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, callback);
            }
        }
        Literal::Pos(BodyAtom::Comparison(cmp)) | Literal::Neg(BodyAtom::Comparison(cmp)) => {
            let negated = matches!(&body[idx], Literal::Neg(_));
            if let (Some(lv), Some(rv)) = (eval_term(&cmp.left, bindings, const_map), eval_term(&cmp.right, bindings, const_map)) {
                let holds = eval_comp(cmp.op, &lv, &rv);
                let pass = if negated { !holds } else { holds };
                if pass {
                    enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, callback);
                }
            }
        }
        Literal::Pos(BodyAtom::Aggregate(_)) | Literal::Neg(BodyAtom::Aggregate(_)) => {
            enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, callback);
        }
        Literal::Pos(BodyAtom::CondLiteral(..)) | Literal::Neg(BodyAtom::CondLiteral(..)) => {
            // Conditional literals are expanded in ground_body, not during enumeration
            enumerate_body(body, idx + 1, bindings, pos_domain, naf_facts, const_map, callback);
        }
    }
}

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
fn expand_choice_condition(
    atom: &ast::Atom,
    condition: &[Literal],
    base_bindings: &Bindings,
    facts: &FactStore,
    const_map: &HashMap<SymbolId, Value>,
    atom_table: &mut AtomTable,
    head_atoms: &mut Vec<AtomId>,
) {
    enumerate_body(condition, 0, base_bindings, facts, facts, const_map, &mut |b| {
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
            enumerate_body(condition, 0, bindings, domain, domain, const_map, &mut |cond_bindings| {
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
