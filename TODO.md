# TODO

## Completed
- [x] Implement domain-aware initial polarity heuristic (choice atoms -> false, derived -> true)
- [x] Implement initial VSIDS activity seeding from clause occurrence counts
- [x] Verify phase saving on backtrack (already working via assign())
- [x] Apply heuristics to both solve() and solve_many()
- [x] Vec-backed Bindings (replace HashMap<SymbolId, Value> with Vec<Option<Value>>)
- [x] Comparison-driven variable binding (solve equalities for unbound variables)

## Pending
- [ ] Cost-bound pruning during optimization search (currently enumerates all models)
