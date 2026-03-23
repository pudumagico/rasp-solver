# ASP Solver — Progress Tracker

## Core Solver (Complete)
- [x] Parser: recursive descent with full ASP-Core-2 subset
  - Facts, rules, constraints, disjunctive heads (`a | b :- c.`)
  - Choice rules with bounds (`L { ... } U`, `{ ... } = N`)
  - Conditional elements in choices (`{a(X) : p(X)}`)
  - Conditional literals in bodies (`a :- p(X) : q(X).`)
  - Arithmetic, comparisons, negation as failure
  - Classical negation (`-a`, `-p(X)`)
  - `#show`, `#show term : body.`, `#const`
  - `#count`, `#sum`, `#min`, `#max` aggregates
  - Aggregate lower bounds (`L op #agg{...}`) and double-bounded (`L op #agg{...} op U`)
  - `#minimize`, `#maximize` with `@` priority levels
  - Weak constraints (`:~ body. [W@P, terms]`)
  - Pools (`p(1..n)`) in facts, rules, constraints, and choices
- [x] Grounder: Tarjan SCC + stratified semi-naive evaluation
  - Domain-aware grounding (choice atoms visible everywhere)
  - Non-stratifiable programs supported
  - Cardinality bound enforcement via subset constraints
  - Conditional choice element expansion
  - Conditional body literal expansion (conjunction over domain)
  - Full aggregate grounding: `#count` (staircase), `#sum` (DP), `#min`/`#max`
  - Bidirectional staircase encoding (completion constraints for aggregate support)
  - Classical negation desugared to `__neg_` predicates + consistency constraints
  - `#show` with computed terms and conditions
- [x] CDCL Solver: two-watched-literal BCP, first-UIP, VSIDS + phase saving, Luby restarts
  - Learned clause GC (activity-based)
  - Multi-model enumeration (`-n N`)
  - Blocking clause model exclusion
- [x] Unfounded set detection: greatest fixpoint, multi-literal loop nogoods
  - Level-0 atoms use multi-literal nogoods (includes blocking decisions)
  - Choice/disjunction semantics
- [x] Output: ASP Competition format (`OPTIMUM FOUND` for optimization)
- [x] CLI: `-n N` flag, stdin/file input, `#minimize`/`#maximize` support
  - Lexicographic optimization with `@` priority levels
  - Iterative model enumeration for optimal cost

## Tests & Benchmarks
- **202 tests** (75 unit + 127 integration), all passing
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

## Remaining
- [ ] Cost-bound pruning during optimization search (currently enumerates all models)
- [ ] Larger competition instances for stress testing
