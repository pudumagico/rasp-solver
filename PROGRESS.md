# ASP Solver — Progress Tracker

## Phase 0–4: Core Solver (Complete)
- [x] Parser: lexer + recursive descent (facts, rules, constraints, choice rules, arithmetic, comparisons, `#show`, `#const`, `#count`, `= N` cardinality syntax, conditional elements)
- [x] Grounder: Tarjan SCC + stratified semi-naive evaluation, domain-aware grounding, non-stratifiable programs, cardinality bound enforcement
- [x] CDCL Solver: two-watched-literal BCP, first-UIP conflict analysis, VSIDS + phase saving, Luby restarts, learned clause GC
- [x] Unfounded set detection: greatest fixpoint algorithm, loop nogoods, choice atom semantics

## Phase 5: Test Harness (Complete)
- [x] 152 tests (73 unit + 79 integration), all passing
- [x] Oracle comparison script, CI fast script
- [x] GitHub Actions CI

## Phase 6–7: Benchmarks & Performance (Complete)
- [x] 16 benchmark instances across 8 problem types
- [x] Benchmark runner + comparison script (vs clingo)
- [x] HashSet dedup, clause GC, targeted VSIDS reinsertion

## Benchmark Results (release build, Apple M-series)

| Instance | Problem | Result | Time |
|----------|---------|--------|------|
| queens_8 | 8-Queens | SAT | 9ms |
| queens_12 | 12-Queens | SAT | 17ms |
| queens_16 | 16-Queens | SAT | 32ms |
| pigeonhole_7_6 | 7-in-6 holes | UNSAT | 81ms |
| graph_color_3 | 3-coloring (6 nodes) | SAT | 9ms |
| hamiltonian | Ham. cycle (4 nodes) | SAT | 9ms |
| schur_4_9 | Schur numbers (4,9) | SAT | 11ms |
| latin_square_4 | Latin square 4×4 | SAT | 9ms |
| knight_tour_5 | Knight's tour 5×5 | SAT | 131ms |
| reachability_20 | Reachability (20 nodes) | SAT | 11ms |
| stable_marriage | Stable marriage (3×3) | SAT | 8ms |

## Remaining
- [ ] Disjunctive heads (`a | b :- c.`)
- [ ] Optimization statements (`#minimize`, `#maximize`)
- [ ] `#sum`, `#min`, `#max` aggregates
- [ ] Multi-answer-set enumeration (`-n 0`)
- [ ] Grounder: first-argument hash index
- [ ] Arena allocators
