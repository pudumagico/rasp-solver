# rasp-solver

A native Rust [Answer Set Programming](https://en.wikipedia.org/wiki/Answer_set_programming) (ASP) solver. Implements the full pipeline from ASP source code to stable models: **Parser → Grounder → CDCL Solver** with unfounded set detection.

This is the first serious ASP solver written entirely in Rust with no external solver dependencies.

## Quick Start

```bash
cargo build --release

# Solve from file
./target/release/asp-solver program.lp

# Solve from stdin
echo "a. b :- a. :- not b." | ./target/release/asp-solver

# Enumerate all models
echo "{a; b; c}." | ./target/release/asp-solver -n 0
```

## Supported Language Features

rasp-solver supports the [ASP-Core-2](https://www.mat.unical.it/aspcomp2013/ASPStandardization) language:

```prolog
% Facts and rules
node(1..5). edge(1,2). edge(2,3).
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).

% Choice rules with bounds
{ assign(N,C) : color(C) } = 1 :- node(N).

% Integrity constraints
:- assign(N1,C), assign(N2,C), edge(N1,N2).

% Classical negation
-safe(X) :- hazard(X).
:- safe(X), -safe(X).

% Aggregates
:- 2 <= #count { X : sel(X) } <= 5.
:- #sum { W,I : item(I,W) } > capacity.
ok :- #min { X : val(X) } >= 3.
ok :- #max { X : val(X) } <= 10.

% Conditional body literals
covered :- reached(X) : target(X).

% Optimization with priorities
#minimize { W@2,E : edge(E), weight(E,W) }.
#minimize { 1@1,N : penalty(N) }.

% Weak constraints
:~ late(X). [1@0, X]

% Directives
#show assign/2.
#show path(X,Y) : important(X).
#const n = 10.
```

| Feature | Status |
|---------|--------|
| Facts and rules | ✓ |
| Integrity constraints | ✓ |
| Choice rules `L { ... } U` | ✓ |
| Conditional elements `{ a(X) : p(X) }` | ✓ |
| Conditional body literals `a :- p(X) : q(X).` | ✓ |
| Negation as failure (`not`) | ✓ |
| Classical negation (`-a`) | ✓ |
| Disjunctive heads (`a \| b :- c.`) | ✓ |
| Arithmetic (`+`, `-`, `*`, `/`, `\`) | ✓ |
| Comparisons (`=`, `!=`, `<`, `>`, `<=`, `>=`) | ✓ |
| Pools / ranges (`p(1..n)`) | ✓ |
| `#count` aggregates | ✓ |
| `#sum` aggregates | ✓ |
| `#min` / `#max` aggregates | ✓ |
| Aggregate lower/double bounds | ✓ |
| `#minimize` / `#maximize` | ✓ |
| `@` priority levels (lexicographic) | ✓ |
| Weak constraints (`:~`) | ✓ |
| `#show` directives (sig + computed) | ✓ |
| `#const` definitions | ✓ |
| Multi-model enumeration (`-n N`) | ✓ |

## Architecture

```
                    ┌──────────────────────┐
  ASP Source ──────>│  Lexer + Parser      │
                    │  (recursive descent) │
                    └─────────┬────────────┘
                              │ AST
                    ┌─────────▼────────────┐
                    │  Grounder            │
                    │  ├ Tarjan SCC        │
                    │  ├ Stratification    │
                    │  └ Semi-naive eval   │
                    └─────────┬────────────┘
                              │ Ground rules
                    ┌─────────▼────────────┐
                    │  Clark's Completion   │
                    │  (SAT translation)   │
                    └─────────┬────────────┘
                              │ Clauses
                    ┌─────────▼────────────┐
                    │  CDCL Solver         │
                    │  ├ 2-watched lits    │
                    │  ├ First-UIP learn   │
                    │  ├ VSIDS + phase     │
                    │  └ Luby restarts     │
                    │         │            │
                    │  Unfounded Set Check │
                    │  (loop nogoods)      │
                    └─────────┬────────────┘
                              │
                     Answer Set / UNSAT
```

## Benchmark Results

Solved on Apple M-series, release build:

| Instance | Problem | Result | Time |
|----------|---------|--------|------|
| queens_8 | 8-Queens | SAT | 34ms |
| queens_12 | 12-Queens | SAT | 40ms |
| queens_16 | 16-Queens | SAT | 60ms |
| queens_20 | 20-Queens | SAT | 101ms |
| queens_30 | 30-Queens | SAT | 362ms |
| queens_50 | 50-Queens | SAT | 3.7s |
| pigeonhole_7_6 | 7→6 holes | UNSAT | 125ms |
| graph_color_3 | 3-coloring (6 nodes) | SAT | 35ms |
| graph_color_100 | 3-coloring (100 nodes) | SAT | 1.1s |
| hamiltonian | Ham. cycle (4 nodes) | SAT | 34ms |
| knight_tour_5 | Knight tour 5×5 | SAT | 155ms |
| latin_square_4 | Latin square 4×4 | SAT | 39ms |
| schur_4_9 | Schur(4,9) | SAT | 65ms |
| stable_marriage | Stable marriage 3×3 | SAT | 32ms |
| reachability_20 | Reachability (20 nodes) | SAT | 37ms |

Run benchmarks yourself:
```bash
scripts/benchmark.sh
```

## Building and Testing

```bash
# Build
cargo build --release

# Run tests (202 tests: 75 unit + 127 integration)
cargo test

# Lint
cargo clippy

# Compare against clingo (if installed)
scripts/oracle_test.sh
```

## Comparison to Other Systems

| System | Language | Type | Notes |
|--------|----------|------|-------|
| [clingo](https://potassco.org/clingo/) | C++ | Full ASP solver | State-of-the-art, ASP Competition winner |
| [DLV](https://www.dlvsystem.it/) | C++ | Full ASP solver | Supports disjunctive programs |
| [clingo-rs](https://github.com/potassco/clingo-rs) | Rust (FFI) | Bindings to clingo | Not a native solver |
| **rasp-solver** | **Rust** | **Native ASP solver** | **First native Rust implementation** |

rasp-solver is not yet competitive with clingo on large instances — clingo has 20+ years of optimization. The goal is to provide a correct, readable, pure-Rust implementation suitable for embedding, research, and education, with performance that improves over time.

## Project Structure

```
src/
├── parser/           # Lexer + recursive descent parser
│   ├── lexer.rs      # Byte-level tokenizer
│   ├── token.rs      # Token definitions
│   ├── ast.rs         # AST type definitions
│   └── mod.rs         # Parser implementation
├── grounder/         # Semi-naive bottom-up grounding
│   ├── scc.rs         # Tarjan SCC + stratification
│   ├── seminaive.rs   # Fixpoint evaluation
│   ├── instantiate.rs # Rule instantiation + joins
│   ├── aggregate.rs   # #count/#sum/#min/#max encoding
│   └── mod.rs         # Pool expansion, optimization
├── solver/           # CDCL-based solver
│   ├── clause.rs      # Watched literals + clause DB
│   ├── analyze.rs     # First-UIP conflict analysis
│   ├── decide.rs      # VSIDS heuristic
│   ├── unfounded.rs   # Stable model semantics
│   └── mod.rs         # Main CDCL loop
├── ground/program.rs # Ground program representation
├── types.rs           # AtomId, SymbolId, Lit, Value
├── interner.rs        # String interning
└── output.rs          # Answer set formatting
```

## License

MIT

## Contributing

Contributions welcome. Please ensure:
- `cargo test` passes
- `cargo clippy` is clean
- New public functions have at least one test
