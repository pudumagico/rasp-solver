#!/bin/bash
# Oracle comparison: test our solver against clingo on sample programs.
# Usage: scripts/oracle_test.sh [path-to-clingo]
set -euo pipefail

CLINGO="${1:-clingo}"
SOLVER="./target/release/asp-solver"

if ! command -v "$CLINGO" &>/dev/null; then
    echo "clingo not found at '$CLINGO', skipping oracle test"
    exit 0
fi

cargo build --release --quiet 2>/dev/null

PASS=0
FAIL=0
SKIP=0

run_test() {
    local name="$1"
    local input="$2"

    # Run clingo (first answer set, 0 = sat, 20 = unsat)
    local clingo_out
    clingo_out=$(echo "$input" | "$CLINGO" --outf=0 -n 1 2>/dev/null) || true
    local clingo_sat="UNKNOWN"
    if echo "$clingo_out" | grep -q "SATISFIABLE"; then
        clingo_sat="SAT"
    elif echo "$clingo_out" | grep -q "UNSATISFIABLE"; then
        clingo_sat="UNSAT"
    fi

    # Run our solver
    local our_out
    our_out=$(echo "$input" | "$SOLVER" 2>/dev/null) || true
    local our_sat="UNKNOWN"
    if echo "$our_out" | grep -q "SATISFIABLE"; then
        our_sat="SAT"
    elif echo "$our_out" | grep -q "UNSATISFIABLE"; then
        our_sat="UNSAT"
    fi

    if [ "$clingo_sat" = "UNKNOWN" ]; then
        echo "  SKIP $name (clingo inconclusive)"
        SKIP=$((SKIP + 1))
        return
    fi

    if [ "$clingo_sat" = "$our_sat" ]; then
        echo "  PASS $name ($our_sat)"
        PASS=$((PASS + 1))
    else
        echo "  FAIL $name: clingo=$clingo_sat, ours=$our_sat"
        FAIL=$((FAIL + 1))
    fi
}

echo "Oracle comparison (vs clingo)"
echo "=============================="

run_test "fact" "a."
run_test "fact_args" "p(1). p(2)."
run_test "rule" "a. b :- a."
run_test "chain" "a. b :- a. c :- b."
run_test "constraint_unsat" "a. :- a."
run_test "naf" "b :- not a."
run_test "naf_with_fact" "a. b :- not a."
run_test "choice" "{a}."
run_test "choice_forced" "{a}. :- not a."
run_test "self_loop" "a :- a."
run_test "mutual_loop" "a :- b. b :- a."
run_test "transitive" "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). path(X,Z) :- path(X,Y), edge(Y,Z)."
run_test "const" "#const n = 5. p(n)."

echo ""
echo "Results: $PASS passed, $FAIL failed, $SKIP skipped"
[ "$FAIL" -eq 0 ] || exit 1
