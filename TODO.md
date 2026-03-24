# TODO

## Completed
- [x] Implement domain-aware initial polarity heuristic (choice atoms -> false, derived -> true)
- [x] Implement initial VSIDS activity seeding from clause occurrence counts
- [x] Verify phase saving on backtrack (already working via assign())
- [x] Apply heuristics to both solve() and solve_many()
- [x] Vec-backed Bindings (replace HashMap<SymbolId, Value> with Vec<Option<Value>>)
- [x] Comparison-driven variable binding (solve equalities for unbound variables)
- [x] Eager comparison evaluation in grounder (prune branches when comparisons fail early)
- [x] Eager equality solving (compute free variable from equality instead of enumerating)
- [x] Fix body pool expansion to be conjunctive (was incorrectly cross-product)

## Pending
- [ ] Cost-bound pruning during optimization search (currently enumerates all models)
