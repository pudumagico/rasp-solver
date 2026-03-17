pub mod aggregate;
pub mod domain;
pub mod instantiate;
pub mod scc;
pub mod seminaive;

use crate::ground::GroundProgram;
use crate::parser::ast::Program;

pub fn ground(_program: &Program) -> GroundProgram {
    todo!("grounder implementation")
}
