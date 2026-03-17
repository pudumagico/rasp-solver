// Solver statistics: conflicts, decisions, propagations, restarts.

#[derive(Debug, Default)]
pub struct SolverStats {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub learned_clauses: u64,
}
