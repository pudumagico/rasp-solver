# ASP Solver — Agent Instructions

## Project Overview
Rust-based ASP (Answer Set Programming) solver targeting ASP Competition benchmarks.
Architecture: Parser → Grounder → CDCL Solver (with unfounded set detection).

## Development Rules
1. Every public function must have at least one test
2. Every commit must pass `cargo test` and `cargo clippy`
3. Never break existing tests to make new tests pass
4. Run oracle comparison after any feature change: `scripts/oracle_test.sh`
5. Keep PROGRESS.md updated after completing each subtask

## Code Style
- No external dependencies beyond `thiserror` for core logic
- Use `u32` interning for all identifiers (SymbolId, AtomId)
- Performance-critical paths (propagation, grounding joins) must be cache-friendly
- Minimize allocations in hot loops

## Testing
- Unit tests: `cargo test`
- Fast CI: `scripts/ci_fast.sh` (<30s)
- Oracle: `scripts/oracle_test.sh` (compare vs clingo)

## Key Files
- `src/types.rs` — foundational types shared across all modules
- `src/interner.rs` — string interning
- `src/parser/` — lexer + recursive descent parser
- `src/grounder/` — semi-naive bottom-up grounding
- `src/solver/` — CDCL + unfounded set detection
- `PROGRESS.md` — current status and task tracking
