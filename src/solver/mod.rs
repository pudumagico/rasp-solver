pub mod analyze;
pub mod assignment;
pub mod clause;
pub mod decide;
pub mod propagate;
pub mod restart;
pub mod stats;
pub mod translate;
pub mod unfounded;
pub mod watched;

use crate::ground::GroundProgram;

#[derive(Debug)]
pub enum SolveResult {
    Satisfiable(Vec<crate::types::AtomId>),
    Unsatisfiable,
}

pub fn solve(_program: &GroundProgram) -> SolveResult {
    todo!("solver implementation")
}
