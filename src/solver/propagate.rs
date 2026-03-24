use super::assignment::Assignment;
use super::clause::ClauseDB;

/// Boolean constraint propagation with binary implication pass first.
pub fn propagate(clause_db: &mut ClauseDB, assignment: &mut Assignment) -> Option<u32> {
    while assignment.propagation_head < assignment.trail().len() {
        let atom = assignment.trail()[assignment.propagation_head];
        assignment.propagation_head += 1;
        let val = assignment.value(atom);
        let p = if val == super::assignment::LBool::True {
            crate::types::Lit::pos(atom)
        } else {
            crate::types::Lit::neg(atom)
        };
        if let Some(conflict) = clause_db.propagate_binary(p, assignment) {
            return Some(conflict);
        }
        if let Some(conflict) = clause_db.propagate_literal(p, assignment) {
            return Some(conflict);
        }
    }
    None
}
