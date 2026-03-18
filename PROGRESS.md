# ASP Solver — Progress Tracker

## Core Solver (Complete)
- [x] Parser: recursive descent with full ASP-Core-2 subset
  - Facts, rules, constraints, disjunctive heads (`a | b :- c.`)
  - Choice rules with bounds (`L { ... } U`, `{ ... } = N`)
  - Conditional elements (`{a(X) : p(X)}`)
  - Arithmetic, comparisons, negation as failure
  - `#show`, `#const`, `#count`, `#sum`, `#min`, `#max`
  - `#minimize`, `#maximize`
- [x] Grounder: Tarjan SCC + stratified semi-naive evaluation
  - Domain-aware grounding (choice atoms visible everywhere)
  - Non-stratifiable programs supported
  - Cardinality bound enforcement via subset constraints
  - Conditional choice element expansion
- [x] CDCL Solver: two-watched-literal BCP, first-UIP, VSIDS + phase saving, Luby restarts
  - Learned clause GC (activity-based)
  - Multi-model enumeration (`-n N`)
  - Blocking clause model exclusion
- [x] Unfounded set detection: greatest fixpoint, loop nogoods, choice/disjunction semantics
- [x] Output: ASP Competition format
- [x] CLI: `-n N` flag, stdin/file input, `#minimize`/`#maximize` support

## Tests & Benchmarks
- **163 tests** (73 unit + 90 integration), all passing, 0 clippy warnings
- **16 benchmark instances** across 8 problem types
- GitHub Actions CI
- Oracle comparison + benchmark scripts

## Benchmark Results (release, Apple M-series)
| Instance | Problem | Time | Result |
|----------|---------|------|--------|
| queens_8 | 8-Queens | 13ms | SAT |
| queens_12 | 12-Queens | 18ms | SAT |
| queens_16 | 16-Queens | 35ms | SAT |
| pigeonhole_7_6 | 7→6 holes | 92ms | UNSAT |
| graph_color_3 | 3-coloring 6n | 9ms | SAT |
| hamiltonian | Ham. cycle 4n | 8ms | SAT |
| schur_4_9 | Schur(4,9) | 14ms | SAT |
| latin_square_4 | Latin 4×4 | 9ms | SAT |
| knight_tour_5 | Knight 5×5 | 138ms | SAT |
| stable_marriage | SM 3×3 | 9ms | SAT |

## Remaining for Full Competition Readiness
- [ ] `#sum`/`#min`/`#max` aggregate grounding (parsed, not yet grounded)
- [ ] Iterative optimization for `#minimize` (currently shows cost of first model)
- [ ] Weak constraints (`~`)
- [ ] Pools in atoms (`p(1..n)`)
- [ ] `@` priority levels in optimization
- [ ] Larger competition instances for stress testing
