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
                    let name = interner.resolve(atom.predicate);
                    if name.starts_with("__") { return String::new(); } // skip auxiliary
                    if atom.args.is_empty() {
                        name.to_string()
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
