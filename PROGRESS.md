# ASP Solver — Progress Tracker

## Phase 0: Scaffolding
- [x] Cargo project initialized
- [x] Module structure created
- [x] `types.rs` — AtomId, SymbolId, Lit, Value
- [x] `interner.rs` — arena-based string interning
- [x] `ground/program.rs` — GroundProgram, AtomTable
- [ ] CLAUDE.md for agent instructions
- [ ] harness/ infrastructure
- [ ] `cargo build` passes
- [ ] `cargo clippy` clean

## Phase 1: Parser
- [ ] 1a: Lexer + token enum
- [ ] 1b: AST types (done — stub in place)
- [ ] 1c: Recursive descent parser

## Phase 2: Grounder
- [ ] 2a: Ground types (done — stub in place)
- [ ] 2b: Domain computation
- [ ] 2c: SCC + stratification
- [ ] 2d: Semi-naive evaluation
- [ ] 2e: Rule instantiation
- [ ] 2f: #count aggregate grounding

## Phase 3: CDCL Solver
- [ ] 3a: Ground → nogood translation
- [ ] 3b: Assignment + trail
- [ ] 3c: Clause storage + watched literals
- [ ] 3d: Unit propagation
- [ ] 3e: Conflict analysis (first-UIP)
- [ ] 3f: VSIDS heuristic
- [ ] 3g: Restart policy
- [ ] 3h: Main CDCL loop

## Phase 4: Unfounded Set Detection
- [ ] Source pointer algorithm
- [ ] Loop nogood generation
- [ ] Integration with CDCL loop
- [ ] Choice rule semantics

## Phase 5: Test Harness
- [ ] Oracle comparison (vs clingo)
- [ ] Fuzz test generator
- [ ] 100 curated test programs
- [ ] ci_fast.sh (<30s)

## Phase 6: ASP Competition Benchmarks
- [ ] Download instances
- [ ] Benchmark runner
- [ ] Pipeline integration

## Phase 7: Performance Optimization
- [ ] Grounder: hash indexes, trie storage
- [ ] Solver: clause GC, propagation optimization
- [ ] System: arena allocators, LTO

## Phase 8: Agent Team
- [ ] Docker infrastructure
- [ ] AGENT_PROMPT.md
- [ ] Multi-agent synchronization
