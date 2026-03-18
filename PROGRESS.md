# ASP Solver — Progress Tracker

## Phase 0: Scaffolding
- [x] Cargo project initialized
- [x] Module structure created
- [x] `types.rs` — AtomId, SymbolId, Lit, Value
- [x] `interner.rs` — arena-based string interning
- [x] `ground/program.rs` — GroundProgram, AtomTable
- [x] CLAUDE.md for agent instructions
- [x] `cargo build` passes
- [x] `cargo clippy` clean
- [x] Unit tests for types.rs and ground/program.rs

## Phase 1: Parser
- [x] 1a: Lexer (full implementation, 15 tests)
- [x] 1b: AST types (complete)
- [x] 1c: Recursive descent parser (16 tests)

## Phase 2: Grounder
- [x] 2a: Ground types
- [x] 2b: Domain computation
- [x] 2c: SCC + stratification (Tarjan's)
- [x] 2d: Semi-naive evaluation
- [x] 2e: Rule instantiation
- [x] 2f: #count aggregate grounding (staircase encoding)
- [x] Error types + #const support
- [x] Domain-aware grounding (choice atoms visible to normal rules + constraints)
- [x] Non-stratifiable programs supported

## Phase 3: CDCL Solver
- [x] 3a: Ground → nogood translation (Clark's completion)
- [x] 3b: Assignment + trail
- [x] 3c: Clause storage + watched literals
- [x] 3d: Unit propagation (BCP)
- [x] 3e: Conflict analysis (first-UIP)
- [x] 3f: VSIDS heuristic (binary max-heap + phase saving)
- [x] 3g: Restart policy (Luby sequence)
- [x] 3h: Main CDCL loop

## Phase 4: Unfounded Set Detection
- [x] Greatest unfounded set computation (fixpoint algorithm)
- [x] Loop nogood generation
- [x] Integration with CDCL loop
- [x] Choice rule semantics (choice atoms excluded from UFS)

## Phase 5: Test Harness
- [x] Output formatting (ASP Competition format)
- [x] End-to-end integration tests (70 tests)
- [x] Oracle comparison script (`scripts/oracle_test.sh`)
- [x] CI fast script (`scripts/ci_fast.sh`)
- [ ] Fuzz test generator

## Phase 6: ASP Competition Benchmarks
- [x] Benchmark instances (13 total: queens 4/8/12/16, pigeonhole 3/2/5/4/7/6/9/8, graph coloring 3/15/20 nodes, Hamiltonian, reachability, stable marriage)
- [x] Benchmark runner + generators (`scripts/benchmark.sh`, `benchmarks/gen_*.py`)
- [x] 12/13 benchmarks pass correctly (pigeonhole_9_8 inherently exponential for CDCL)

## Phase 7: Performance Optimization
- [x] Grounder: HashSet-based duplicate detection (was O(n) Vec::contains)
- [x] Grounder: duplicate rule elimination in fixpoint loop
- [x] Grounder: domain-aware grounding (choice atoms visible to normal rules)
- [x] Solver: targeted VSIDS reinsertion on backtrack (was O(n) full scan)
- [x] Solver: learned clause GC (activity-based, triggered at restarts)
- [x] Solver: clause activity decay
- [ ] Grounder: first-argument hash index for fact lookup
- [ ] System: arena allocators

## Benchmark Results (release build)
| Instance        | Result | Time    |
|-----------------|--------|---------|
| queens_8        | SAT    | 11ms    |
| queens_12       | SAT    | 18ms    |
| queens_16       | SAT    | 37ms    |
| pigeonhole_7_6  | UNSAT  | 88ms    |
| graph_color_3   | SAT    | 9ms     |
| hamiltonian     | SAT    | 8ms     |
| reachability_20 | SAT    | 10ms    |

## Current Stats
- **143 tests** (73 unit + 70 integration), all passing
- **0 clippy warnings**
- **13 benchmark instances**, 12 solving correctly
- Phases 0–7 substantially complete
