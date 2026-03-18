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
```

## Supported Language Features

rasp-solver supports a practical subset of the [ASP-Core-2](https://www.mat.unical.it/aspcomp2013/ASPStandardization) language:

```prolog
% Facts
node(1). node(2). edge(1,2).

% Rules with variables
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).

% Integrity constraints
:- path(X,X).

% Negation as failure
safe(X) :- node(X), not dangerous(X).

% Choice rules with cardinality bounds
{ assign(N,C) : color(C) } = 1 :- node(N).

% Arithmetic and comparisons
next(X+1) :- num(X), X < 10.

% Aggregates (#count)
:- #count { X : selected(X) } > 3.

% Directives
#show path/2.
#const max = 10.
```

| Feature | Status |
|---------|--------|
| Facts and rules | Supported |
| Integrity constraints | Supported |
| Choice rules `L { ... } U` | Supported |
| `= N` cardinality syntax | Supported |
| Conditional elements `{ a(X) : p(X) }` | Supported |
| Negation as failure (`not`) | Supported |
| Arithmetic (`+`, `-`, `*`, `/`, `\`) | Supported |
| Comparisons (`=`, `!=`, `<`, `>`, `<=`, `>=`) | Supported |
| `#count` aggregates | Supported |
| `#show` directives | Supported |
| `#const` definitions | Supported |
| Non-stratifiable programs | Supported |
| Disjunctive heads (`a \| b`) | Not yet |
| Optimization (`#minimize`) | Not yet |
| `#sum`, `#min`, `#max` aggregates | Not yet |

## Architecture

```
ASP Source → [Lexer] → [Parser] → AST
                                    ↓
                              [Grounder]
                           SCC + Stratification
                         Semi-naive Evaluation
                         Domain-aware Matching
                                    ↓
                            Ground Program
                                    ↓
                              [Translator]
                          Clark's Completion
                                    ↓
                            [CDCL Solver]
                        Two-watched Literals
                        First-UIP Learning
                        VSIDS + Phase Saving
                        Luby Restarts
                        Clause GC
                                    ↓
                        [Unfounded Set Checker]
                       Greatest Fixpoint Algorithm
                                    ↓
                           Answer Set / UNSAT
```

## Benchmark Results

Solved on Apple M-series, release build:

| Instance | Problem | Atoms | Result | Time |
|----------|---------|-------|--------|------|
| queens_8 | 8-Queens | 64 | SAT | 11ms |
| queens_12 | 12-Queens | 144 | SAT | 18ms |
| queens_16 | 16-Queens | 256 | SAT | 37ms |
| graph_color_3 | 3-coloring (6 nodes) | 18 | SAT | 9ms |
| hamiltonian | Ham. cycle (4 nodes) | 6 | SAT | 8ms |
| pigeonhole_7_6 | 7 pigeons / 6 holes | 42 | UNSAT | 88ms |
| reachability_20 | Reachability (20 nodes) | 400 | SAT | 10ms |
| stable_marriage | Stable marriage (3×3) | 9 | SAT | 8ms |

Run benchmarks yourself:
```bash
scripts/benchmark.sh
```

## Building and Testing

```bash
# Build
cargo build --release

# Run tests (152 tests: 73 unit + 79 integration)
cargo test

# Lint
cargo clippy

# Compare against clingo (if installed)
scripts/oracle_test.sh

# Fast CI check
scripts/ci_fast.sh
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
├── parser/       # Lexer + recursive descent parser
│   ├── lexer.rs  # Byte-level tokenizer
│   ├── ast.rs    # AST type definitions
│   └── mod.rs    # Parser implementation
├── grounder/     # Semi-naive bottom-up grounding
│   ├── scc.rs    # Tarjan SCC + stratification
│   ├── seminaive.rs  # Fixpoint evaluation
│   └── instantiate.rs # Rule instantiation + joins
├── solver/       # CDCL-based solver
│   ├── clause.rs     # Watched literals + clause DB
│   ├── analyze.rs    # First-UIP conflict analysis
│   ├── decide.rs     # VSIDS heuristic
│   ├── unfounded.rs  # Stable model semantics
│   └── mod.rs        # Main CDCL loop
├── types.rs      # AtomId, SymbolId, Lit, Value
├── interner.rs   # String interning
└── output.rs     # Answer set formatting
```

## License

MIT

## Contributing

Contributions welcome. Please ensure:
- `cargo test` passes
- `cargo clippy` is clean
- New public functions have at least one test
