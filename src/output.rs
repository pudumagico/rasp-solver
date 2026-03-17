use crate::ground::GroundProgram;
use crate::solver::SolveResult;

/// Print result in ASP Competition format.
pub fn print_result(result: &SolveResult, program: &GroundProgram) {
    match result {
        SolveResult::Satisfiable(atoms) => {
            println!("SATISFIABLE");
            let show: Vec<String> = atoms
                .iter()
                .filter(|id| program.show_all || program.show_atoms.contains(id))
                .map(|id| format_atom(program, *id))
                .collect();
            // TODO: use interner for proper formatting
            let _ = show;
            todo!("format answer set atoms")
        }
        SolveResult::Unsatisfiable => {
            println!("UNSATISFIABLE");
        }
    }
}

fn format_atom(_program: &GroundProgram, _id: crate::types::AtomId) -> String {
    todo!()
}
