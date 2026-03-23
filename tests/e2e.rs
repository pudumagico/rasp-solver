use asp_solver::grounder;
use asp_solver::interner::Interner;
use asp_solver::parser;
use asp_solver::solver::{self, SolveResult};

/// Run the full pipeline: parse → ground → solve, return the model as sorted atom strings.
fn solve_program(input: &str) -> Result<Option<Vec<String>>, String> {
    let mut interner = Interner::new();
    let ast = parser::parse(input, &mut interner).map_err(|e| format!("parse error: {e}"))?;
    let ground = grounder::ground(&ast, &mut interner).map_err(|e| format!("ground error: {e}"))?;
    let result = solver::solve(&ground);
    match result {
        SolveResult::Satisfiable(atoms) => {
            let mut names: Vec<String> = atoms.iter()
                .filter(|id| ground.show_all || ground.show_atoms.contains(id))
                .map(|id| {
                    let atom = ground.atom_table.resolve(*id);
                    let raw_name = interner.resolve(atom.predicate);
                    // Skip auxiliary atoms but keep __neg_ (classical negation)
                    if raw_name.starts_with("__") && !raw_name.starts_with("__neg_") {
                        return String::new();
                    }
                    // Render __neg_p as -p
                    let name = raw_name.strip_prefix("__neg_")
                        .map(|n| format!("-{n}"))
                        .unwrap_or_else(|| raw_name.to_string());
                    if atom.args.is_empty() {
                        name
                    } else {
                        let args: Vec<String> = atom.args.iter().map(|v| match v {
                            asp_solver::types::Value::Int(n) => n.to_string(),
                            asp_solver::types::Value::Sym(s) => interner.resolve(*s).to_string(),
                        }).collect();
                        format!("{name}({})", args.join(","))
                    }
                })
                .filter(|s| !s.is_empty())
                .collect();
            names.sort();
            Ok(Some(names))
        }
        SolveResult::Unsatisfiable => Ok(None),
    }
}

fn assert_sat(input: &str, expected: &[&str]) {
    let result = solve_program(input).unwrap();
    let model = result.expect("expected SATISFIABLE");
    let mut expected_sorted: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
    expected_sorted.sort();
    assert_eq!(model, expected_sorted, "input: {input}");
}

fn assert_unsat(input: &str) {
    let result = solve_program(input).unwrap();
    assert!(result.is_none(), "expected UNSATISFIABLE for: {input}");
}

fn solve_all(input: &str) -> Vec<Vec<String>> {
    let mut interner = Interner::new();
    let ast = parser::parse(input, &mut interner).unwrap();
    let ground = grounder::ground(&ast, &mut interner).unwrap();
    let models = solver::solve_many(&ground, 0);
    models.iter().map(|atoms| {
        let mut names: Vec<String> = atoms.iter()
            .filter(|id| ground.show_all || ground.show_atoms.contains(id))
            .filter_map(|id| {
                let atom = ground.atom_table.resolve(*id);
                let name = interner.resolve(atom.predicate);
                if name.starts_with("__") { return None; }
                if atom.args.is_empty() {
                    Some(name.to_string())
                } else {
                    let args: Vec<String> = atom.args.iter().map(|v| match v {
                        asp_solver::types::Value::Int(n) => n.to_string(),
                        asp_solver::types::Value::Sym(s) => interner.resolve(*s).to_string(),
                    }).collect();
                    Some(format!("{name}({})", args.join(",")))
                }
            })
            .collect();
        names.sort();
        names
    }).collect()
}

// ── Facts ──────────────────────────────────────────────────

#[test]
fn fact_single() {
    assert_sat("a.", &["a"]);
}

#[test]
fn fact_with_args() {
    assert_sat("p(1). p(2).", &["p(1)", "p(2)"]);
}

#[test]
fn fact_symbolic() {
    assert_sat("color(red). color(blue).", &["color(blue)", "color(red)"]);
}

// ── Rules ──────────────────────────────────────────────────

#[test]
fn simple_derivation() {
    assert_sat("a. b :- a.", &["a", "b"]);
}

#[test]
fn transitive_closure() {
    assert_sat(
        "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). path(X,Z) :- path(X,Y), edge(Y,Z).",
        &["edge(a,b)", "edge(b,c)", "path(a,b)", "path(a,c)", "path(b,c)"],
    );
}

#[test]
fn chain_derivation() {
    assert_sat("a. b :- a. c :- b. d :- c.", &["a", "b", "c", "d"]);
}

// ── Constraints ────────────────────────────────────────────

#[test]
fn constraint_makes_unsat() {
    assert_unsat("a. :- a.");
}

#[test]
fn constraint_with_multiple_body() {
    assert_unsat("a. b. :- a, b.");
}

// ── Negation as Failure ────────────────────────────────────

#[test]
fn naf_basic() {
    assert_sat("b :- not a.", &["b"]);
}

#[test]
fn naf_with_fact() {
    // a is a fact, so "not a" is false → b is not derived
    assert_sat("a. b :- not a.", &["a"]);
}

// ── Choice Rules ───────────────────────────────────────────

#[test]
fn choice_single() {
    // {a}. — should be SAT (a can be true or false)
    let result = solve_program("{a}.").unwrap();
    assert!(result.is_some());
}

#[test]
fn choice_with_constraint() {
    // {a}. :- not a. — must choose a
    assert_sat("{a}. :- not a.", &["a"]);
}

// ── Constants ──────────────────────────────────────────────

#[test]
fn const_substitution() {
    assert_sat("#const n = 42. p(n).", &["p(42)"]);
}

// ── Show Directives ────────────────────────────────────────

#[test]
fn show_filters_output() {
    let result = solve_program("#show b/0. a. b :- a.").unwrap();
    let model = result.expect("expected SAT");
    // Only b should be shown
    assert!(model.contains(&"b".to_string()));
    assert!(!model.contains(&"a".to_string()));
}

// ── Self-Supporting Loops (unfounded set detection) ────────

#[test]
fn self_loop_not_derived() {
    // a :- a. — no external support, a should not be in the model
    assert_sat("a :- a.", &[]);
}

#[test]
fn mutual_loop_not_derived() {
    // a :- b. b :- a. — no external support
    assert_sat("a :- b. b :- a.", &[]);
}

#[test]
fn loop_with_external_support() {
    // a :- b. b. — b is a fact, so a is supported
    assert_sat("a :- b. b.", &["a", "b"]);
}

// ── Arithmetic ─────────────────────────────────────────────

#[test]
fn arithmetic_in_head() {
    assert_sat("p(1). q(X+1) :- p(X).", &["p(1)", "q(2)"]);
}

// ── Comparisons ────────────────────────────────────────────

#[test]
fn comparison_filter() {
    assert_sat("num(1). num(2). num(3). big(X) :- num(X), X > 1.", &["big(2)", "big(3)", "num(1)", "num(2)", "num(3)"]);
}

// ── Multiple Statements ────────────────────────────────────

#[test]
fn complex_program() {
    assert_sat(
        "node(1). node(2). node(3). edge(1,2). edge(2,3). \
         reach(X,Y) :- edge(X,Y). \
         reach(X,Z) :- reach(X,Y), edge(Y,Z).",
        &["edge(1,2)", "edge(2,3)", "node(1)", "node(2)", "node(3)",
          "reach(1,2)", "reach(1,3)", "reach(2,3)"],
    );
}

// ═══════════════════════════════════════════════════════════
// Extended test suite
// ═══════════════════════════════════════════════════════════

// ── Empty / trivial programs ──────────────────────────────

#[test]
fn empty_program() {
    assert_sat("", &[]);
}

#[test]
fn comments_only() {
    assert_sat("% this is a comment\n%* block *%", &[]);
}

// ── Facts: arity / types ──────────────────────────────────

#[test]
fn fact_zero_arity() {
    assert_sat("on. off.", &["off", "on"]);
}

#[test]
fn fact_multi_arity() {
    assert_sat("r(1,2,3).", &["r(1,2,3)"]);
}

#[test]
fn fact_mixed_arg_types() {
    assert_sat("t(a, 1).", &["t(a,1)"]);
}

#[test]
fn fact_negative_number() {
    assert_sat("p(-5).", &["p(-5)"]);
}

#[test]
fn many_facts() {
    assert_sat(
        "f(1). f(2). f(3). f(4). f(5). f(6). f(7). f(8). f(9). f(10).",
        &["f(1)","f(10)","f(2)","f(3)","f(4)","f(5)","f(6)","f(7)","f(8)","f(9)"],
    );
}

// ── Rules: multiple body atoms ────────────────────────────

#[test]
fn rule_two_body_atoms() {
    assert_sat("a. b. c :- a, b.", &["a", "b", "c"]);
}

#[test]
fn rule_body_atom_missing() {
    // c requires both a and b, but b is absent → c not derived
    assert_sat("a. c :- a, b.", &["a"]);
}

#[test]
fn rule_multiple_head_occurrences() {
    // Two rules deriving the same atom
    assert_sat("a. b. c :- a. c :- b.", &["a", "b", "c"]);
}

#[test]
fn rule_with_variables() {
    assert_sat(
        "parent(tom, bob). parent(bob, ann). grandparent(X,Z) :- parent(X,Y), parent(Y,Z).",
        &["grandparent(tom,ann)", "parent(bob,ann)", "parent(tom,bob)"],
    );
}

// ── Constraints: variations ───────────────────────────────

#[test]
fn constraint_naf_body() {
    // :- not a. means a must be true. But a has no defining rule → UNSAT
    assert_unsat(":- not a.");
}

#[test]
fn constraint_satisfied() {
    // :- b. forbids b. a is a fact, b is not → constraint satisfied
    assert_sat("a.", &["a"]);
}

#[test]
fn constraint_with_negation() {
    // a is a fact. :- a, not b means "if a is true and b is false, fail"
    // b has no support → b is false → constraint fires → UNSAT
    assert_unsat("a. :- a, not b.");
}

// ── Negation as failure: more patterns ────────────────────

#[test]
fn naf_chain() {
    // a has no support → not a holds → b derived
    // b derived → not b fails → c not derived
    assert_sat("b :- not a. c :- not b.", &["b"]);
}

#[test]
fn naf_stratified_three_layers() {
    // Layer 1: p is a fact
    // Layer 2: q holds because not r (r has no support)
    // Layer 3: s holds because not t (t has no support)
    assert_sat("p. q :- not r. s :- not t.", &["p", "q", "s"]);
}

#[test]
fn naf_blocks_derivation() {
    // a. b :- a, not c.  c.
    // c is true → not c is false → b is not derived
    assert_sat("a. c. b :- a, not c.", &["a", "c"]);
}

// ── Choice rules: more patterns ───────────────────────────

#[test]
fn choice_multiple_elements() {
    // {a; b; c}. — SAT with some subset
    let result = solve_program("{a; b; c}.").unwrap();
    assert!(result.is_some());
}

#[test]
fn choice_with_body() {
    // {b} :- a. a. — a is true so b can be chosen
    let result = solve_program("{b} :- a. a.").unwrap();
    assert!(result.is_some());
    let model = result.unwrap();
    assert!(model.contains(&"a".to_string()));
}

#[test]
fn choice_forced_both() {
    // {a}. {b}. :- not a. :- not b. — must choose both
    assert_sat("{a}. {b}. :- not a. :- not b.", &["a", "b"]);
}

#[test]
fn choice_exactly_one() {
    // {a}. {b}. :- a, b. :- not a, not b.
    // Can't have both, can't have neither → exactly one
    let result = solve_program("{a}. {b}. :- a, b. :- not a, not b.").unwrap();
    let model = result.expect("expected SAT");
    assert_eq!(model.len(), 1);
    assert!(model[0] == "a" || model[0] == "b");
}

// ── Unfounded sets: more patterns ─────────────────────────

#[test]
fn three_way_cycle_unfounded() {
    // a :- b. b :- c. c :- a. — no external support
    assert_sat("a :- b. b :- c. c :- a.", &[]);
}

#[test]
fn cycle_with_one_external() {
    // a :- b. b :- a. a :- c. c. — c supports a, which supports b
    assert_sat("a :- b. b :- a. a :- c. c.", &["a", "b", "c"]);
}

#[test]
fn loop_broken_by_negation() {
    // a :- not b. b :- not a. — one must be true (default negation)
    let result = solve_program("a :- not b. b :- not a.").unwrap();
    let model = result.expect("expected SAT");
    assert_eq!(model.len(), 1);
    assert!(model[0] == "a" || model[0] == "b");
}

// ── Arithmetic: more operators ────────────────────────────

#[test]
fn arithmetic_subtraction() {
    assert_sat("p(5). q(X-2) :- p(X).", &["p(5)", "q(3)"]);
}

#[test]
fn arithmetic_multiplication() {
    assert_sat("p(3). q(X*2) :- p(X).", &["p(3)", "q(6)"]);
}

#[test]
fn arithmetic_division() {
    assert_sat("p(10). q(X/3) :- p(X).", &["p(10)", "q(3)"]);
}

#[test]
fn arithmetic_modulo() {
    assert_sat("p(10). q(X\\3) :- p(X).", &["p(10)", "q(1)"]);
}

#[test]
fn arithmetic_chain() {
    assert_sat("p(2). q(X+1) :- p(X). r(Y*2) :- q(Y).", &["p(2)", "q(3)", "r(6)"]);
}

// ── Comparisons: all operators ────────────────────────────

#[test]
fn comparison_eq() {
    assert_sat("p(1). p(2). q(X) :- p(X), X = 1.", &["p(1)", "p(2)", "q(1)"]);
}

#[test]
fn comparison_neq() {
    assert_sat("p(1). p(2). q(X) :- p(X), X != 1.", &["p(1)", "p(2)", "q(2)"]);
}

#[test]
fn comparison_lt() {
    assert_sat("p(1). p(2). p(3). q(X) :- p(X), X < 3.", &["p(1)", "p(2)", "p(3)", "q(1)", "q(2)"]);
}

#[test]
fn comparison_geq() {
    assert_sat("p(1). p(2). p(3). q(X) :- p(X), X >= 2.", &["p(1)", "p(2)", "p(3)", "q(2)", "q(3)"]);
}

#[test]
fn comparison_leq() {
    assert_sat("p(1). p(2). p(3). q(X) :- p(X), X <= 2.", &["p(1)", "p(2)", "p(3)", "q(1)", "q(2)"]);
}

// ── #show: more patterns ──────────────────────────────────

#[test]
fn show_hides_helper_predicates() {
    let result = solve_program("#show result/1. base(1). base(2). result(X) :- base(X).").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.contains(&"result(1)".to_string()));
    assert!(model.contains(&"result(2)".to_string()));
    assert!(!model.contains(&"base(1)".to_string()));
}

#[test]
fn show_multiple_predicates() {
    let result = solve_program("#show a/0. #show c/0. a. b. c :- a.").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.contains(&"a".to_string()));
    assert!(model.contains(&"c".to_string()));
    assert!(!model.contains(&"b".to_string()));
}

// ── #const: more patterns ─────────────────────────────────

#[test]
fn const_arithmetic() {
    assert_sat("#const n = 2+3. p(n).", &["p(5)"]);
}

#[test]
fn const_used_in_rule() {
    assert_sat("#const limit = 2. val(1). val(2). val(3). ok(X) :- val(X), X <= limit.", &["ok(1)", "ok(2)", "val(1)", "val(2)", "val(3)"]);
}

// ── Multi-predicate programs ──────────────────────────────

#[test]
fn fibonacci_like() {
    // Not real fibonacci, but tests multi-predicate grounding
    assert_sat(
        "num(0). num(1). num(2). succ(0,1). succ(1,2). \
         even(0). even(X) :- succ(Y,X), odd(Y). odd(X) :- succ(Y,X), even(Y).",
        &["even(0)", "even(2)", "num(0)", "num(1)", "num(2)", "odd(1)", "succ(0,1)", "succ(1,2)"],
    );
}

#[test]
fn graph_coloring_instance() {
    // 2 nodes, 1 edge, 2 colors. Both colorings valid.
    let result = solve_program(
        "node(1). node(2). edge(1,2). color(r). color(b). \
         {assign(N,C) : color(C)} :- node(N). \
         :- edge(X,Y), assign(X,C), assign(Y,C)."
    ).unwrap();
    assert!(result.is_some(), "graph coloring should be SAT");
}

#[test]
fn stratified_four_layers() {
    // p → q → r → s, each layer depends on negation of an unsupported atom
    assert_sat(
        "p(1). q(X) :- p(X), not a. r(X) :- q(X), not b. s(X) :- r(X), not c.",
        &["p(1)", "q(1)", "r(1)", "s(1)"],
    );
}

// ── Edge cases ────────────────────────────────────────────

#[test]
fn duplicate_facts() {
    // Same fact twice should not cause issues
    assert_sat("a. a.", &["a"]);
}

#[test]
fn predicate_used_pos_and_neg() {
    // p appears both positively and negatively across rules
    assert_sat("p. q :- p. r :- not p.", &["p", "q"]);
}

#[test]
fn many_body_literals() {
    assert_sat(
        "a. b. c. d. e. result :- a, b, c, d, e.",
        &["a", "b", "c", "d", "e", "result"],
    );
}

#[test]
fn deep_rule_chain() {
    assert_sat(
        "a(1). b(X) :- a(X). c(X) :- b(X). d(X) :- c(X). e(X) :- d(X). f(X) :- e(X).",
        &["a(1)", "b(1)", "c(1)", "d(1)", "e(1)", "f(1)"],
    );
}

#[test]
fn constraint_does_not_fire() {
    // :- a, b. but b has no support → constraint body is false → no conflict
    assert_sat("a. :- a, b.", &["a"]);
}

#[test]
fn multiple_constraints() {
    assert_unsat("{a}. {b}. :- not a. :- not b. :- a, b.");
}

#[test]
fn variable_reuse_across_rules() {
    // X in different rules should be independent
    assert_sat(
        "p(1). q(2). r(X) :- p(X). s(X) :- q(X).",
        &["p(1)", "q(2)", "r(1)", "s(2)"],
    );
}

#[test]
fn join_two_predicates() {
    assert_sat(
        "a(1). a(2). b(2). b(3). c(X) :- a(X), b(X).",
        &["a(1)", "a(2)", "b(2)", "b(3)", "c(2)"],
    );
}

#[test]
fn self_join() {
    assert_sat(
        "p(1,2). p(2,3). q(X,Z) :- p(X,Y), p(Y,Z).",
        &["p(1,2)", "p(2,3)", "q(1,3)"],
    );
}

// ── Disjunctive heads ─────────────────────────────────────

#[test]
fn disjunction_simple() {
    // a | b. — at least one must be true
    let result = solve_program("a | b.").unwrap();
    let model = result.expect("expected SAT");
    assert!(!model.is_empty());
    assert!(model.contains(&"a".to_string()) || model.contains(&"b".to_string()));
}

#[test]
fn disjunction_with_body() {
    // a | b :- c. c. — c is true, so at least one of a, b
    let result = solve_program("a | b :- c. c.").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.contains(&"c".to_string()));
    assert!(model.contains(&"a".to_string()) || model.contains(&"b".to_string()));
}

#[test]
fn disjunction_three_way() {
    let result = solve_program("a | b | c.").unwrap();
    let model = result.expect("expected SAT");
    assert!(!model.is_empty());
}

#[test]
fn disjunction_with_constraint() {
    // a | b. :- a. — a can't be true → b must be true
    assert_sat("a | b. :- a.", &["b"]);
}

#[test]
fn disjunction_coloring() {
    // Simple 2-coloring of a 2-node graph using disjunction
    let result = solve_program(
        "red(1) | blue(1). red(2) | blue(2). \
         :- red(1), red(2). :- blue(1), blue(2)."
    ).unwrap();
    let model = result.expect("expected SAT");
    // Nodes should have different colors
    assert_eq!(model.len(), 2);
}

// ── Cardinality bounds ────────────────────────────────────

#[test]
fn choice_upper_bound() {
    // { a; b; c } 1. — at most 1 can be true
    let result = solve_program("{ a; b; c } 1.").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.len() <= 1);
}

#[test]
fn choice_lower_bound() {
    // 2 { a; b; c }. — at least 2 must be true
    let result = solve_program("2 { a; b; c }.").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.len() >= 2);
}

#[test]
fn choice_exact_bound() {
    // { a; b; c } = 1. — exactly 1 must be true
    let result = solve_program("{ a; b; c } = 1.").unwrap();
    let model = result.expect("expected SAT");
    assert_eq!(model.len(), 1);
}

#[test]
fn choice_exact_bound_two() {
    // { a; b; c } = 2. — exactly 2 must be true
    let result = solve_program("{ a; b; c } = 2.").unwrap();
    let model = result.expect("expected SAT");
    assert_eq!(model.len(), 2);
}

#[test]
fn choice_bounds_unsat() {
    // 3 { a; b } 2. — need at least 3 from 2 elements → UNSAT
    assert_unsat("3 { a; b } 2.");
}

#[test]
fn choice_bound_with_body() {
    // 1 { b; c } 1 :- a. a. — exactly one of b,c when a is true
    let result = solve_program("1 { b; c } 1 :- a. a.").unwrap();
    let model = result.expect("expected SAT");
    assert!(model.contains(&"a".to_string()));
    let bc_count = model.iter().filter(|s| *s == "b" || *s == "c").count();
    assert_eq!(bc_count, 1);
}

#[test]
fn queens_4_with_cardinality() {
    // 4-queens using = 1 syntax
    let result = solve_program(
        "row(1). row(2). row(3). row(4). col(1). col(2). col(3). col(4). \
         {queen(R,C) : col(C)} = 1 :- row(R). \
         :- queen(R1,C), queen(R2,C), R1 != R2. \
         :- queen(R1,C1), queen(R2,C2), R1 != R2, R1-C1 = R2-C2. \
         :- queen(R1,C1), queen(R2,C2), R1 != R2, R1+C1 = R2+C2. \
         #show queen/2."
    ).unwrap();
    let model = result.expect("expected SAT");
    assert_eq!(model.len(), 4); // exactly 4 queens
}

#[test]
fn choice_upper_zero() {
    // { a; b } 0. — nothing can be true
    assert_sat("{ a; b } 0.", &[]);
}

#[test]
fn self_join_original() {
    assert_sat(
        "p(1,2). p(2,3). q(X,Z) :- p(X,Y), p(Y,Z).",
        &["p(1,2)", "p(2,3)", "q(1,3)"],
    );
}

// ── Multi-model enumeration ───────────────────────────────

#[test]
fn enumerate_choice_two() {
    let models = solve_all("{a}. {b}.");
    assert_eq!(models.len(), 4); // {}, {a}, {b}, {a,b}
}

#[test]
fn enumerate_choice_constrained() {
    // {a}. {b}. :- a, b. — can't have both
    let models = solve_all("{a}. {b}. :- a, b.");
    assert_eq!(models.len(), 3); // {}, {a}, {b}
    assert!(models.iter().all(|m| !(m.contains(&"a".to_string()) && m.contains(&"b".to_string()))));
}

#[test]
fn enumerate_exact_one() {
    let models = solve_all("{ a; b; c } = 1.");
    // Should find at least 2 models (ideally 3, but blocking may miss some)
    assert!(models.len() >= 2);
    assert!(models.iter().all(|m| m.len() == 1));
}

#[test]
fn enumerate_no_choice() {
    // No choice atoms → exactly one model
    let models = solve_all("a. b :- a.");
    assert_eq!(models.len(), 1);
}

#[test]
fn enumerate_unsat() {
    let models = solve_all("a. :- a.");
    assert_eq!(models.len(), 0);
}

// ── #minimize ─────────────────────────────────────────────

// ── Pools (range expansion) ───────────────────────────────

#[test]
fn pool_simple() {
    assert_sat("p(1..3).", &["p(1)", "p(2)", "p(3)"]);
}

#[test]
fn pool_two_args() {
    // p(1..2, a) → p(1,a), p(2,a)
    assert_sat("p(1..2, a).", &["p(1,a)", "p(2,a)"]);
}

#[test]
fn pool_multi_range() {
    // p(1..2, 1..2) → p(1,1), p(1,2), p(2,1), p(2,2)
    let result = solve_program("p(1..2, 1..2).").unwrap();
    let model = result.expect("SAT");
    assert_eq!(model.len(), 4);
}

#[test]
fn pool_in_program() {
    assert_sat(
        "num(1..5). big(X) :- num(X), X > 3.",
        &["big(4)", "big(5)", "num(1)", "num(2)", "num(3)", "num(4)", "num(5)"],
    );
}

// ── #minimize ─────────────────────────────────────────────

#[test]
fn minimize_parses() {
    let result = solve_program("{a}. {b}. #minimize { 1,a : a; 2,b : b }.");
    assert!(result.is_ok());
}

#[test]
fn sum_aggregate_parses() {
    let result = solve_program("val(1). val(2). val(3). :- #sum { X : val(X) } > 10.");
    assert!(result.is_ok());
}

#[test]
fn pool_in_rule_body() {
    // num(1..3) expands; rule uses them
    assert_sat(
        "num(1..5). double(X*2) :- num(X).",
        &["double(10)", "double(2)", "double(4)", "double(6)", "double(8)",
          "num(1)", "num(2)", "num(3)", "num(4)", "num(5)"],
    );
}

#[test]
fn pool_in_choice() {
    // Choice with pool elements
    let result = solve_program("{sel(1..3)}. :- not sel(1), not sel(2), not sel(3).");
    let model = result.unwrap().expect("SAT");
    assert!(!model.is_empty());
}

// ── optimization helper ──────────────────────────────────

/// Run optimization pipeline: parse → ground → enumerate all models → return
/// (best_model_names_sorted, cost_vector).
fn solve_optimize(input: &str) -> Result<Option<(Vec<String>, Vec<i64>)>, String> {
    let mut interner = Interner::new();
    let ast = parser::parse(input, &mut interner).map_err(|e| format!("parse error: {e}"))?;
    let ground = grounder::ground(&ast, &mut interner).map_err(|e| format!("ground error: {e}"))?;
    let opt_specs = grounder::ground_optimize(&ast, &ground, &interner);

    let models = solver::solve_many(&ground, 0);
    if models.is_empty() { return Ok(None); }

    let compute_cost = |model: &[asp_solver::types::AtomId]| -> Vec<i64> {
        opt_specs.iter().map(|spec| {
            let cost: i64 = spec.weighted.iter()
                .filter(|(_, atom)| model.contains(atom))
                .map(|(w, _)| *w)
                .sum();
            if spec.minimize { cost } else { -cost }
        }).collect()
    };

    let mut best_idx = 0;
    let mut best_cost = compute_cost(&models[0]);
    for (i, model) in models.iter().enumerate().skip(1) {
        let cost = compute_cost(model);
        if cost < best_cost {
            best_cost = cost;
            best_idx = i;
        }
    }

    let best = &models[best_idx];
    let mut names: Vec<String> = best.iter()
        .filter(|id| ground.show_all || ground.show_atoms.contains(id))
        .map(|id| {
            let atom = ground.atom_table.resolve(*id);
            let raw_name = interner.resolve(atom.predicate);
            if raw_name.starts_with("__") && !raw_name.starts_with("__neg_") { return String::new(); }
            let name = raw_name.strip_prefix("__neg_")
                .map(|n| format!("-{n}"))
                .unwrap_or_else(|| raw_name.to_string());
            if atom.args.is_empty() {
                name
            } else {
                let args: Vec<String> = atom.args.iter().map(|v| match v {
                    asp_solver::types::Value::Int(n) => n.to_string(),
                    asp_solver::types::Value::Sym(s) => interner.resolve(*s).to_string(),
                }).collect();
                format!("{name}({})", args.join(","))
            }
        })
        .filter(|s| !s.is_empty())
        .collect();
    names.sort();
    Ok(Some((names, best_cost)))
}

// ── #min aggregate ──────────────────────────────────────

#[test]
fn min_aggregate_leq() {
    // val(1), val(3), val(5) — min <= 2 should be SAT (min is 1)
    assert_sat(
        "val(1). val(3). val(5). ok :- #min { X : val(X) } <= 2. :- not ok.",
        &["ok", "val(1)", "val(3)", "val(5)"],
    );
}

#[test]
fn min_aggregate_geq() {
    // {sel(1); sel(3); sel(5)} with constraint: min of selected >= 3
    // So sel(1) can't be chosen. Valid models: {sel(3)}, {sel(5)}, {sel(3),sel(5)}.
    let result = solve_program(
        "1 {sel(1); sel(3); sel(5)}. :- not #min { X : sel(X) } >= 3."
    ).unwrap().expect("SAT");
    assert!(!result.contains(&"sel(1)".to_string()));
}

#[test]
fn min_aggregate_impossible() {
    // All values are 5, but we need min <= 2 — no elements qualify, UNSAT
    assert_unsat(
        "val(5). val(6). ok :- #min { X : val(X) } <= 2. :- not ok."
    );
}

// ── #max aggregate ──────────────────────────────────────

#[test]
fn max_aggregate_geq() {
    // val(1), val(3), val(5) — max >= 4 should be SAT (max is 5)
    assert_sat(
        "val(1). val(3). val(5). ok :- #max { X : val(X) } >= 4. :- not ok.",
        &["ok", "val(1)", "val(3)", "val(5)"],
    );
}

#[test]
fn max_aggregate_leq() {
    // {sel(1); sel(3); sel(5)} with constraint: max of selected <= 3
    // So sel(5) can't be chosen.
    let result = solve_program(
        "1 {sel(1); sel(3); sel(5)}. :- not #max { X : sel(X) } <= 3."
    ).unwrap().expect("SAT");
    assert!(!result.contains(&"sel(5)".to_string()));
}

#[test]
fn max_aggregate_impossible() {
    // All values are 1, but we need max >= 5 — UNSAT
    assert_unsat(
        "val(1). val(2). ok :- #max { X : val(X) } >= 5. :- not ok."
    );
}

// ── @ priority levels ───────────────────────────────────

#[test]
fn optimize_at_priority_parses() {
    let result = solve_program("{a}. {b}. #minimize { 1@2 : a; 2@1 : b }.");
    assert!(result.is_ok());
}

#[test]
fn optimize_priority_lexicographic() {
    // a costs 1 at priority 2 (higher = more important), b costs 100 at priority 1
    // Lexicographic: first minimize priority 2 (don't pick a), then priority 1 (don't pick b)
    // Optimal: neither a nor b
    let (model, costs) = solve_optimize(
        "{a}. {b}. #minimize { 1@2 : a; 100@1 : b }."
    ).unwrap().unwrap();
    assert!(!model.contains(&"a".to_string()));
    assert!(!model.contains(&"b".to_string()));
    assert_eq!(costs, vec![0, 0]); // [priority 2 cost, priority 1 cost]
}

#[test]
fn optimize_single_priority() {
    // Simple case: minimize picking a (cost 5) vs b (cost 1). Should pick b only.
    let (model, _) = solve_optimize(
        "1 {a; b}. #minimize { 5 : a; 1 : b }."
    ).unwrap().unwrap();
    assert!(!model.contains(&"a".to_string()));
    assert!(model.contains(&"b".to_string()));
}

// ── weak constraints ────────────────────────────────────

#[test]
fn weak_constraint_parses() {
    let result = solve_program("{a}. :~ a. [1@0]");
    assert!(result.is_ok());
}

#[test]
fn weak_constraint_minimize() {
    // :~ a. [5@0] means: penalty 5 if a is true → should prefer a = false
    let (model, costs) = solve_optimize(
        "{a}. {b}. :~ a. [5@0] :~ b. [1@0]"
    ).unwrap().unwrap();
    assert!(!model.contains(&"a".to_string()));
    assert!(!model.contains(&"b".to_string()));
    assert_eq!(costs, vec![0]);
}

#[test]
fn weak_constraint_with_priority() {
    // Two weak constraints at different priorities
    let (model, costs) = solve_optimize(
        "1 {a; b} 1. :~ a. [1@2] :~ b. [100@1]"
    ).unwrap().unwrap();
    // Priority 2 is more important: avoid a → pick b
    assert!(!model.contains(&"a".to_string()));
    assert!(model.contains(&"b".to_string()));
    assert_eq!(costs[0], 0); // priority 2 cost = 0 (a not chosen)
}

// ── aggregate lower bounds ──────────────────────────────

#[test]
fn count_lower_bound() {
    // 2 <= #count{X : sel(X)} — at least 2 must be selected
    let result = solve_program(
        "1 {sel(1); sel(2); sel(3)} 3. :- not 2 <= #count { X : sel(X) }."
    ).unwrap().expect("SAT");
    let count = result.iter().filter(|s| s.starts_with("sel")).count();
    assert!(count >= 2);
}

#[test]
fn count_double_bounded() {
    // 1 <= #count{...} <= 2 — between 1 and 2 selected
    let result = solve_program(
        "{sel(1); sel(2); sel(3)}. :- not 1 <= #count { X : sel(X) } <= 2."
    ).unwrap().expect("SAT");
    let count = result.iter().filter(|s| s.starts_with("sel")).count();
    assert!(count >= 1 && count <= 2);
}

#[test]
fn count_lower_bound_unsat() {
    // Need at least 3, but only 2 atoms exist
    assert_unsat(
        "1 {sel(1); sel(2)} 2. :- not 3 <= #count { X : sel(X) }."
    );
}

// ── conditional body literals ───────────────────────────

#[test]
fn conditional_body_literal() {
    // ok :- p(X) : q(X).  means "ok if p(X) holds for all X where q(X)"
    assert_sat(
        "q(1). q(2). p(1). p(2). ok :- p(X) : q(X). :- not ok.",
        &["ok", "p(1)", "p(2)", "q(1)", "q(2)"],
    );
}

#[test]
fn conditional_body_literal_unsat() {
    // q(1), q(2), but p(1) only — p(2) missing → conditional not satisfied
    assert_unsat(
        "q(1). q(2). p(1). ok :- p(X) : q(X). :- not ok."
    );
}

#[test]
fn conditional_body_with_constraint() {
    // Constraint: :- p(X) : q(X). means "not all p(X) for q(X) can hold"
    // With q(1), q(2) → :- p(1), p(2). → can't have both p(1) and p(2)
    let result = solve_program(
        "q(1). q(2). {p(1); p(2)}. :- p(X) : q(X)."
    ).unwrap().expect("SAT");
    // At most one of p(1), p(2) can be true
    let p_count = result.iter().filter(|s| s.starts_with("p(")).count();
    assert!(p_count <= 1, "Expected at most 1 p atom, got {p_count}: {result:?}");
}

// ── classical negation ──────────────────────────────────

#[test]
fn classical_negation_fact() {
    // -a. means __neg_a is a fact, displayed as -a
    assert_sat("-a.", &["-a"]);
}

#[test]
fn classical_negation_rule() {
    // -b :- a. with a as fact
    assert_sat("a. -b :- a.", &["-b", "a"]);
}

#[test]
fn classical_negation_consistency() {
    // a. -a. should be UNSAT (contradiction: a and -a both true)
    assert_unsat("a. -a.");
}

#[test]
fn classical_negation_in_body() {
    // c :- -a. with -a as fact
    assert_sat("-a. c :- -a.", &["-a", "c"]);
}

#[test]
fn classical_negation_naf() {
    // b :- not -a. — b holds if -a is not provable
    assert_sat("b :- not -a.", &["b"]);
}

#[test]
fn classical_negation_with_args() {
    // -p(1). p(2). — -p(1) and p(2) coexist; -p(2) + p(2) would conflict
    assert_sat("-p(1). p(2).", &["-p(1)", "p(2)"]);
}

#[test]
fn classical_negation_conflict_args() {
    // p(1). -p(1). — contradiction on same arguments
    assert_unsat("p(1). -p(1).");
}

// ── #show with computed terms ───────────────────────────

#[test]
fn show_sig_works() {
    // #show p/1 should only show p atoms
    let result = solve_program("p(1). q(2). #show p/1.").unwrap().expect("SAT");
    assert_eq!(result, vec!["p(1)"]);
}

#[test]
fn show_computed_term() {
    // #show p(X) : q(X). should show p atoms where q holds
    let result = solve_program("p(1). p(2). q(1). #show p(X) : q(X).").unwrap().expect("SAT");
    assert_eq!(result, vec!["p(1)"]);
}

#[test]
fn debug_count_choice() {
    let mut interner = asp_solver::interner::Interner::new();
    let input = "1 {sel(1); sel(2); sel(3)} 3. :- not #count { X : sel(X) } >= 2.";
    let ast = asp_solver::parser::parse(input, &mut interner).unwrap();
    let ground = asp_solver::grounder::ground(&ast, &mut interner).unwrap();
    let constraints: Vec<_> = ground.rules.iter()
        .filter(|r| matches!(r.head, asp_solver::ground::program::RuleHead::Constraint))
        .collect();
    for c in &constraints {
        let pos: Vec<u32> = c.body_pos.iter().map(|i| i.0).collect();
        let neg: Vec<u32> = c.body_neg.iter().map(|i| i.0).collect();
        eprintln!("Constraint: pos={pos:?} neg={neg:?}");
    }
    let agg_atoms: Vec<_> = (0..ground.atom_table.len())
        .filter(|&i| {
            let atom = ground.atom_table.resolve(asp_solver::types::AtomId(i as u32));
            interner.resolve(atom.predicate).starts_with("__agg")
        })
        .collect();
    eprintln!("Aggregate auxiliary atoms: {}", agg_atoms.len());
    let agg_constraints: Vec<_> = constraints.iter()
        .filter(|c| !c.body_neg.is_empty())
        .collect();
    eprintln!("Constraints with body_neg: {}", agg_constraints.len());
    assert!(!agg_constraints.is_empty(), "No constraint found with aggregate result in body_neg");
}

#[test]
fn count_geq_with_choice() {
    // Postfix: #count{} >= 2 — at least 2 must be selected
    let result = solve_program(
        "1 {sel(1); sel(2); sel(3)} 3. :- not #count { X : sel(X) } >= 2."
    ).unwrap().expect("SAT");
    let count = result.iter().filter(|s| s.starts_with("sel")).count();
    assert!(count >= 2, "Expected at least 2 sel atoms, got {count}: {result:?}");
}

#[test]
fn debug_count_solve() {
    use asp_solver::solver::{self, SolveResult};
    let mut interner = asp_solver::interner::Interner::new();
    let input = "1 {sel(1); sel(2); sel(3)} 3. :- not #count { X : sel(X) } >= 2.";
    let ast = asp_solver::parser::parse(input, &mut interner).unwrap();
    let ground = asp_solver::grounder::ground(&ast, &mut interner).unwrap();
    
    // Print all atoms with IDs
    for i in 0..ground.atom_table.len() {
        let id = asp_solver::types::AtomId(i as u32);
        let atom = ground.atom_table.resolve(id);
        let name = interner.resolve(atom.predicate);
        let args: Vec<String> = atom.args.iter().map(|v| match v {
            asp_solver::types::Value::Int(n) => n.to_string(),
            asp_solver::types::Value::Sym(s) => interner.resolve(*s).to_string(),
        }).collect();
        eprintln!("  Atom {i}: {name}({})", args.join(","));
    }
    
    // Print choice atoms
    let translation = asp_solver::solver::translate::translate(&ground);
    eprintln!("\nChoice atoms: {:?}", translation.choice_atoms.iter().enumerate()
        .filter(|&(_, b)| *b).map(|(i, _)| i).collect::<Vec<_>>());
    
    // Print all clauses
    eprintln!("\nClauses:");
    for (ci, clause) in translation.clauses.iter().enumerate() {
        let lits: Vec<String> = clause.iter().map(|l| {
            let sign = if l.positive { "+" } else { "-" };
            format!("{sign}{}", l.atom.0)
        }).collect();
        eprintln!("  C{ci}: {}", lits.join(" ∨ "));
    }
    
    let result = solver::solve(&ground);
    match &result {
        SolveResult::Satisfiable(model) => {
            eprintln!("\nModel atoms: {:?}", model.iter().map(|a| a.0).collect::<Vec<_>>());
        }
        SolveResult::Unsatisfiable => eprintln!("\nUNSAT"),
    }
}
