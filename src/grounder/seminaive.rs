use std::collections::{HashMap, HashSet};

use crate::ground::program::{AtomTable, GroundAtom, GroundProgram, GroundRule, RuleHead};
use crate::interner::Interner;
use crate::parser::ast::{self, Statement, Term};
use crate::types::{AtomId, SymbolId, Value};

use super::instantiate::{self, AggContext, FactStore};
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
                    .map(|t| instantiate::eval_term(t, &instantiate::Bindings::new(), const_map))
                    .collect();
                if let Some(args) = args
                    && add_to_both(h.predicate, args.clone(), &mut facts, &mut known) {
                        let ga = GroundAtom { predicate: h.predicate, args };
                        let id = atom_table.get_or_insert(ga);
                        all_rules.push(GroundRule { head: RuleHead::Normal(id), body_pos: vec![], body_neg: vec![] });
                    }
            }
    }

    // Magic set optimization: for constraints `:- not p(Vs), q(Vs).` where p is
    // defined by a rule and q has ground facts, restrict p's grounding to demanded
    // tuples by rewriting p's rule to include a demand guard atom.
    let magic_program = apply_magic_sets_global(program, &facts, interner);
    let program = magic_program.as_ref().unwrap_or(program);
    // If magic sets created demand facts, add them
    for stmt in &program.statements {
        if let Statement::Rule(r) = stmt
            && r.body.is_empty() && r.head.len() == 1 {
                let h = &r.head[0];
                let name = interner.resolve(h.predicate);
                if name.starts_with("__magic_") {
                    let args: Option<Vec<Value>> = h.args.iter()
                        .map(|t| instantiate::eval_term(t, &instantiate::Bindings::new(), const_map))
                        .collect();
                    if let Some(args) = args {
                        add_to_both(h.predicate, args.clone(), &mut facts, &mut known);
                        let ga = GroundAtom { predicate: h.predicate, args };
                        let id = atom_table.get_or_insert(ga);
                        all_rules.push(GroundRule { head: RuleHead::Normal(id), body_pos: vec![], body_neg: vec![] });
                    }
                }
            }
    }

    // Re-stratify if program was modified
    let strata = if magic_program.is_some() {
        super::scc::stratify(program).unwrap_or_else(|_| strata.to_vec())
    } else {
        strata.to_vec()
    };

    for stratum in &strata {
        evaluate_stratum(
            stratum, program, &mut facts, &mut known, &mut atom_table,
            &mut all_rules, interner, const_map,
        );
    }

    // Resolve show atoms
    if !show_all {
        for stmt in &program.statements {
            match stmt {
                Statement::ShowSig(s) => {
                    for i in 0..atom_table.len() {
                        let atom = atom_table.resolve(crate::types::AtomId(i as u32));
                        if atom.predicate == s.predicate && atom.args.len() == s.arity {
                            show_atoms.push(crate::types::AtomId(i as u32));
                        }
                    }
                }
                Statement::Show(s) => {
                    // #show term : body. — enumerate body, evaluate term, match atoms
                    let show_domain = &facts;
                    instantiate::enumerate_body_public(
                        &s.body, 0, &instantiate::Bindings::new(), show_domain, show_domain, const_map,
                        &mut |bindings| {
                            match &s.term {
                                ast::Term::Function(pred, term_args) => {
                                    let args: Option<Vec<Value>> = term_args.iter()
                                        .map(|t| instantiate::eval_term(t, bindings, const_map))
                                        .collect();
                                    if let Some(args) = args {
                                        let ga = GroundAtom { predicate: *pred, args };
                                        if let Some(id) = atom_table.get(&ga)
                                            && !show_atoms.contains(&id) {
                                                show_atoms.push(id);
                                            }
                                    }
                                }
                                ast::Term::Symbolic(pred) => {
                                    let ga = GroundAtom { predicate: *pred, args: vec![] };
                                    if let Some(id) = atom_table.get(&ga)
                                        && !show_atoms.contains(&id) {
                                            show_atoms.push(id);
                                        }
                                }
                                _ => {}
                            }
                        },
                    );
                }
                _ => {}
            }
        }
    }

    // Add classical negation consistency constraints: :- p(X), -p(X).
    // For each __neg_P atom, find matching P atoms and add constraints.
    add_classical_neg_constraints(&atom_table, interner, &mut all_rules);

    GroundProgram { atom_table, rules: all_rules, show_atoms, show_all }
}

/// For each classically negated predicate `__neg_P`, add integrity constraints
/// `:- P(args), __neg_P(args)` to prevent contradictions.
fn add_classical_neg_constraints(
    atom_table: &AtomTable,
    interner: &Interner,
    rules: &mut Vec<GroundRule>,
) {
    // Collect all atoms grouped by predicate
    let mut by_predicate: HashMap<SymbolId, Vec<AtomId>> = HashMap::new();
    for i in 0..atom_table.len() {
        let id = crate::types::AtomId(i as u32);
        let atom = atom_table.resolve(id);
        by_predicate.entry(atom.predicate).or_default().push(id);
    }

    // Match __neg_X predicates with X predicates
    // matches: __neg_ prefix (5 chars of the resolved name)
    for (&pred, neg_ids) in &by_predicate {
        let name = interner.resolve(pred);
        if let Some(pos_name) = name.strip_prefix("__neg_") {
            // Find the positive predicate
            for (&pos_pred, pos_ids) in &by_predicate {
                if interner.resolve(pos_pred) == pos_name {
                    // For each pair with matching args, add constraint
                    for &neg_id in neg_ids {
                        let neg_atom = atom_table.resolve(neg_id);
                        for &pos_id in pos_ids {
                            let pos_atom = atom_table.resolve(pos_id);
                            if neg_atom.args == pos_atom.args {
                                rules.push(GroundRule {
                                    head: RuleHead::Constraint,
                                    body_pos: vec![pos_id, neg_id],
                                    body_neg: vec![],
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn evaluate_stratum(
    stratum: &Stratum,
    program: &ast::Program,
    facts: &mut FactStore,
    known: &mut FactSet,
    atom_table: &mut AtomTable,
    all_rules: &mut Vec<GroundRule>,
    interner: &mut Interner,
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
                    interner, atom_table,
                );
                all_rules.extend(bound_constraints);
            }
        }
        all_rules.extend(ground_rules);
    }

    // 1b. Add symmetry breaking constraints for uniform 2-arg choice predicates
    add_symmetry_breaking(all_rules, atom_table, program);

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
        let domain_idx = instantiate::build_arg_index(&domain);

        for rule in &normal_rules {
            let has_agg = rule.body.iter().any(|l| matches!(l,
                ast::Literal::Pos(ast::BodyAtom::Aggregate(_)) |
                ast::Literal::Neg(ast::BodyAtom::Aggregate(_))
            ));
            let mut agg_ctx_owned;
            let agg_ctx = if has_agg {
                agg_ctx_owned = AggContext { facts: &domain, interner, const_map };
                Some(&mut agg_ctx_owned)
            } else {
                None
            };
            let ground_rules = instantiate::instantiate_rule_with_index(
                &rule.head, &rule.body, facts, &domain, atom_table, const_map, agg_ctx, &domain_idx,
            );
            for gr in ground_rules {
                let key = rule_key(&gr);
                if !seen_rules.insert(key) { continue; }

                let body_satisfiable = gr.body_pos.iter().all(|bp| {
                    let a = atom_table.resolve(*bp);
                    domain_known.get(&a.predicate).is_some_and(|s| s.contains(&a.args))
                });

                let head_ids = match &gr.head {
                    RuleHead::Normal(id) => vec![*id],
                    RuleHead::Disjunction(ids) => ids.clone(),
                    _ => vec![],
                };
                if body_satisfiable {
                    for head_id in &head_ids {
                        let head_atom = atom_table.resolve(*head_id);
                        let pred = head_atom.predicate;
                        let args = head_atom.args.clone();
                        if add_to_both(pred, args.clone(), facts, known) {
                            changed = true;
                        }
                        add_to_both(pred, args, &mut domain, &mut domain_known);
                    }
                }
                all_rules.push(gr);
            }
        }
    }

    // Ground constraints — build index once for the final domain
    let domain_idx = instantiate::build_arg_index(&domain);
    for c in &constraints {
        let has_agg = c.body.iter().any(|l| matches!(l,
            ast::Literal::Pos(ast::BodyAtom::Aggregate(_)) |
            ast::Literal::Neg(ast::BodyAtom::Aggregate(_))
        ));
        let mut agg_ctx_owned;
        let agg_ctx = if has_agg {
            agg_ctx_owned = AggContext { facts: &domain, interner, const_map };
            Some(&mut agg_ctx_owned)
        } else {
            None
        };
        let ground_rules = instantiate::instantiate_constraint_with_index(&c.body, facts, &domain, atom_table, const_map, agg_ctx, &domain_idx);
        all_rules.extend(ground_rules);
    }
}


/// Magic set rewriting at the AST level. Detects constraints of the form
/// `:- not p(V1,...,Vn), q(V1,...,Vn).` where p is defined by a rule and q
/// has ground facts. Adds `__magic_p(V1,...,Vn)` to p's rule body and creates
/// demand facts `__magic_p(t1,...,tn).` for each ground q tuple.
fn apply_magic_sets_global(
    program: &ast::Program,
    facts: &FactStore,
    interner: &mut Interner,
) -> Option<ast::Program> {
    // 1. Find rule-defined predicates
    let mut rule_defined: HashSet<SymbolId> = HashSet::new();
    for stmt in &program.statements {
        if let Statement::Rule(r) = stmt
            && !r.body.is_empty() {
                for head in &r.head {
                    rule_defined.insert(head.predicate);
                }
            }
    }

    // 2. Scan constraints for demand patterns
    let mut demands: HashMap<SymbolId, (SymbolId, SymbolId)> = HashMap::new(); // target_pred -> (magic_pred, source_pred)
    for stmt in &program.statements {
        let body = match stmt {
            Statement::Constraint(c) => &c.body,
            _ => continue,
        };
        let mut neg_atoms: Vec<&ast::Atom> = Vec::new();
        let mut pos_atoms: Vec<&ast::Atom> = Vec::new();
        for lit in body {
            match lit {
                ast::Literal::Neg(ast::BodyAtom::Atom(a)) => neg_atoms.push(a),
                ast::Literal::Pos(ast::BodyAtom::Atom(a)) => pos_atoms.push(a),
                _ => {}
            }
        }
        for neg in &neg_atoms {
            if !rule_defined.contains(&neg.predicate) { continue; }
            for pos in &pos_atoms {
                if neg.args.len() != pos.args.len() { continue; }
                if facts.get(&pos.predicate).is_none_or(|t| t.is_empty()) { continue; }
                // Check: same variables in same positions
                let vars_match = neg.args.iter().zip(pos.args.iter()).all(|(n, p)| {
                    matches!((n, p), (Term::Variable(a), Term::Variable(b)) if a == b)
                });
                if !vars_match { continue; }

                let neg_name = interner.resolve(neg.predicate).to_string();
                let magic_pred = interner.intern(&format!("__magic_{neg_name}"));
                demands.insert(neg.predicate, (magic_pred, pos.predicate));
                break;
            }
        }
    }

    if demands.is_empty() { return None; }

    // 3. Rewrite the program: add demand guards + demand facts
    let mut new_stmts = Vec::new();
    for stmt in &program.statements {
        match stmt {
            Statement::Rule(r) if !r.body.is_empty() => {
                if r.head.len() == 1
                    && let Some(&(magic_pred, source_pred)) = demands.get(&r.head[0].predicate) {
                        // Add demand guard to the body
                        let magic_atom = ast::Atom {
                            predicate: magic_pred,
                            args: r.head[0].args.clone(),
                        };
                        let mut new_body = vec![ast::Literal::Pos(ast::BodyAtom::Atom(magic_atom))];
                        new_body.extend(r.body.clone());
                        new_stmts.push(Statement::Rule(ast::Rule {
                            head: r.head.clone(),
                            body: new_body,
                        }));

                        // Create demand facts from the source predicate
                        if let Some(tuples) = facts.get(&source_pred) {
                            for tuple in tuples {
                                let args: Vec<Term> = tuple.iter().map(|v| match v {
                                    Value::Int(n) => Term::Integer(*n),
                                    Value::Sym(s) => Term::Symbolic(*s),
                                }).collect();
                                let fact_atom = ast::Atom { predicate: magic_pred, args };
                                new_stmts.push(Statement::Rule(ast::Rule {
                                    head: vec![fact_atom],
                                    body: vec![],
                                }));
                            }
                        }
                        continue;
                    }
                new_stmts.push(stmt.clone());
            }
            _ => new_stmts.push(stmt.clone()),
        }
    }

    Some(ast::Program { statements: new_stmts })
}

/// Detect symmetric 2-arg choice predicates and add lex-leader ordering constraints.
/// Valid when the first argument is used only in `!=` comparisons in constraints
/// (i.e., first-arg values are interchangeable). Adds for consecutive first-arg
/// values a_i < a_{i+1}: `:- pred(a_{i+1}, h1), pred(a_i, h2)` where h1 < h2.
fn add_symmetry_breaking(
    rules: &mut Vec<GroundRule>,
    atom_table: &mut AtomTable,
    program: &ast::Program,
) {
    // Collect all choice-head atom ids grouped by predicate
    let mut choice_preds: HashMap<SymbolId, Vec<AtomId>> = HashMap::new();
    for rule in rules.iter() {
        if let RuleHead::Choice(heads) = &rule.head {
            for &id in heads {
                let atom = atom_table.resolve(id);
                if atom.args.len() == 2 {
                    choice_preds.entry(atom.predicate).or_default().push(id);
                }
            }
        }
    }

    for (&pred, atom_ids) in &choice_preds {
        if !first_arg_symmetric(pred, program) { continue; }

        // Group by first argument
        let mut by_first: HashMap<&Value, Vec<(&Value, AtomId)>> = HashMap::new();
        for &id in atom_ids {
            let atom = atom_table.resolve(id);
            by_first.entry(&atom.args[0]).or_default().push((&atom.args[1], id));
        }

        let mut first_args: Vec<&Value> = by_first.keys().copied().collect();
        first_args.sort();
        if first_args.len() < 2 { continue; }

        // All groups must have the same set of second-arg values
        let reference_seconds: HashSet<&Value> = by_first[first_args[0]].iter().map(|(v, _)| *v).collect();
        if !first_args.iter().all(|k| {
            let secs: HashSet<&Value> = by_first[k].iter().map(|(v, _)| *v).collect();
            secs == reference_seconds
        }) { continue; }

        let mut lookup: HashMap<(&Value, &Value), AtomId> = HashMap::new();
        for &id in atom_ids {
            let atom = atom_table.resolve(id);
            lookup.insert((&atom.args[0], &atom.args[1]), id);
        }

        let mut seconds: Vec<&Value> = reference_seconds.into_iter().collect();
        seconds.sort();

        for w in first_args.windows(2) {
            let (a_i, a_next) = (w[0], w[1]);
            for (si, &h1) in seconds.iter().enumerate() {
                for &h2 in &seconds[si + 1..] {
                    let id_next_h1 = lookup[&(a_next, h1)];
                    let id_i_h2 = lookup[&(a_i, h2)];
                    rules.push(GroundRule {
                        head: RuleHead::Constraint,
                        body_pos: vec![id_next_h1, id_i_h2],
                        body_neg: vec![],
                    });
                }
            }
        }
    }
}

/// Check that the first argument of a 2-arg predicate is symmetric:
/// in all constraints mentioning this predicate, the first arg only appears
/// in `!=` comparisons with other first-arg variables of the same predicate,
/// never in arithmetic expressions.
fn first_arg_symmetric(pred: SymbolId, program: &ast::Program) -> bool {
    for stmt in &program.statements {
        let body = match stmt {
            ast::Statement::Constraint(c) => &c.body,
            _ => continue,
        };
        // Collect which variables appear as first arg of our predicate
        let mut first_arg_vars: HashSet<SymbolId> = HashSet::new();
        let mut mentions_pred = false;
        for lit in body {
            if let ast::Literal::Pos(ast::BodyAtom::Atom(a)) | ast::Literal::Neg(ast::BodyAtom::Atom(a)) = lit
                && a.predicate == pred && a.args.len() == 2 {
                    mentions_pred = true;
                    if let Term::Variable(v) = &a.args[0] {
                        first_arg_vars.insert(*v);
                    }
                }
        }
        if !mentions_pred { continue; }
        // Check that first-arg variables only appear in our predicate's first arg
        // or in `!=` comparisons with other first-arg vars of the same predicate.
        // If they appear in ANY other predicate or arithmetic, symmetry is broken.
        for lit in body {
            match lit {
                ast::Literal::Pos(ast::BodyAtom::Comparison(cmp)) | ast::Literal::Neg(ast::BodyAtom::Comparison(cmp)) => {
                    let lv = term_vars(&cmp.left);
                    let rv = term_vars(&cmp.right);
                    let all_vars: HashSet<SymbolId> = lv.union(&rv).copied().collect();
                    if all_vars.is_disjoint(&first_arg_vars) { continue; }
                    if cmp.op != ast::CompOp::Neq { return false; }
                    if !matches!(&cmp.left, Term::Variable(v) if first_arg_vars.contains(v)) { return false; }
                    if !matches!(&cmp.right, Term::Variable(v) if first_arg_vars.contains(v)) { return false; }
                }
                ast::Literal::Pos(ast::BodyAtom::Atom(a)) | ast::Literal::Neg(ast::BodyAtom::Atom(a)) => {
                    if a.predicate == pred { continue; }
                    // First-arg vars appearing in a DIFFERENT predicate breaks symmetry
                    for arg in &a.args {
                        let vars = term_vars(arg);
                        if !vars.is_disjoint(&first_arg_vars) { return false; }
                    }
                }
                _ => {}
            }
        }
    }
    true
}

fn term_vars(t: &Term) -> HashSet<SymbolId> {
    let mut vars = HashSet::new();
    collect_vars(t, &mut vars);
    vars
}

fn collect_vars(t: &Term, vars: &mut HashSet<SymbolId>) {
    match t {
        Term::Variable(v) => { vars.insert(*v); }
        Term::BinOp(_, l, r) => { collect_vars(l, vars); collect_vars(r, vars); }
        Term::UnaryMinus(inner) => { collect_vars(inner, vars); }
        Term::Function(_, args) => { for a in args { collect_vars(a, vars); } }
        _ => {}
    }
}

/// Generate constraint rules to enforce choice rule bounds using staircase encoding.
/// Lower bound L: at least L head atoms must be true (when body holds).
/// Upper bound U: at most U head atoms can be true (when body holds).
/// Uses O(n*k) auxiliary rules instead of exponential C(n,k) subset constraints.
#[allow(clippy::too_many_arguments)]
fn generate_bound_constraints(
    heads: &[AtomId],
    lower: &Option<Term>,
    upper: &Option<Term>,
    body_pos: &[AtomId],
    body_neg: &[AtomId],
    const_map: &HashMap<SymbolId, Value>,
    interner: &mut Interner,
    atom_table: &mut AtomTable,
) -> Vec<GroundRule> {
    let mut rules = Vec::new();
    let n = heads.len();

    let eval_bound = |term: &Term| -> Option<usize> {
        let val = instantiate::eval_term(term, &instantiate::Bindings::new(), const_map)?;
        match val {
            Value::Int(v) if v >= 0 => Some(v as usize),
            _ => None,
        }
    };

    // Upper bound: at most U can be true → "at least U+1 are true" must be false
    if let Some(u_term) = upper
        && let Some(u) = eval_bound(u_term)
        && u < n
        && let Some((aux_rules, result_id)) = build_staircase(heads, u + 1, interner, atom_table)
    {
        rules.extend(aux_rules);
        // :- body, result (too many are true → violation)
        let mut bp = body_pos.to_vec();
        bp.push(result_id);
        rules.push(GroundRule { head: RuleHead::Constraint, body_pos: bp, body_neg: body_neg.to_vec() });
    }

    // Lower bound: at least L must be true → "at least L are true" must hold
    if let Some(l_term) = lower
        && let Some(l) = eval_bound(l_term)
        && l > 0
    {
        if l > n {
            // Impossible: need more atoms than exist → always UNSAT when body holds
            rules.push(GroundRule { head: RuleHead::Constraint, body_pos: body_pos.to_vec(), body_neg: body_neg.to_vec() });
        } else if let Some((aux_rules, result_id)) = build_staircase(heads, l, interner, atom_table) {
            rules.extend(aux_rules);
            // :- body, not result (too few are true → violation)
            let mut bn = body_neg.to_vec();
            bn.push(result_id);
            rules.push(GroundRule { head: RuleHead::Constraint, body_pos: body_pos.to_vec(), body_neg: bn });
        }
    }

    rules
}

/// Build staircase encoding: aux[i][j] = "at least j of the first i elements are true".
/// Returns auxiliary rules and the AtomId for aux[n][target] ("at least target are true").
fn build_staircase(
    elements: &[AtomId],
    target: usize,
    interner: &mut Interner,
    atom_table: &mut AtomTable,
) -> Option<(Vec<GroundRule>, AtomId)> {
    let n = elements.len();
    if target > n { return None; }
    if target == 0 {
        let name = interner.intern("__card_true");
        let id = atom_table.get_or_insert(GroundAtom { predicate: name, args: vec![] });
        return Some((vec![GroundRule { head: RuleHead::Normal(id), body_pos: vec![], body_neg: vec![] }], id));
    }

    let mut rules = Vec::new();
    let agg_id = atom_table.len();
    let mut aux = vec![vec![AtomId(0); target + 1]; n + 1];

    for (i, row) in aux.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let name = interner.intern(&format!("__card_{agg_id}_{i}_{j}"));
            *cell = atom_table.get_or_insert(GroundAtom { predicate: name, args: vec![] });
        }
    }

    // Base: aux[i][0] always true
    for row in &aux {
        rules.push(GroundRule { head: RuleHead::Normal(row[0]), body_pos: vec![], body_neg: vec![] });
    }

    // Staircase: forward support + reverse completion constraints
    for i in 1..=n {
        for j in 1..=target.min(i) {
            // Skip: aux[i][j] :- aux[i-1][j]
            rules.push(GroundRule {
                head: RuleHead::Normal(aux[i][j]),
                body_pos: vec![aux[i - 1][j]],
                body_neg: vec![],
            });
            // Include: aux[i][j] :- elem[i-1], aux[i-1][j-1]
            rules.push(GroundRule {
                head: RuleHead::Normal(aux[i][j]),
                body_pos: vec![elements[i - 1], aux[i - 1][j - 1]],
                body_neg: vec![],
            });
            // Completion: :- aux[i][j], not aux[i-1][j], not elem[i-1]
            rules.push(GroundRule {
                head: RuleHead::Constraint,
                body_pos: vec![aux[i][j]],
                body_neg: vec![aux[i - 1][j], elements[i - 1]],
            });
            // Completion: :- aux[i][j], not aux[i-1][j], not aux[i-1][j-1]
            rules.push(GroundRule {
                head: RuleHead::Constraint,
                body_pos: vec![aux[i][j]],
                body_neg: vec![aux[i - 1][j], aux[i - 1][j - 1]],
            });
        }
    }

    Some((rules, aux[n][target]))
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
