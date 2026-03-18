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

use crate::ground::program::GroundProgram;
use crate::types::{AtomId, Lit};

use assignment::{Assignment, LBool};
use clause::ClauseDB;
use decide::VsidsHeap;
use restart::RestartPolicy;
use unfounded::UnfoundedSetChecker;

#[derive(Debug)]
pub enum SolveResult {
    Satisfiable(Vec<AtomId>),
    Unsatisfiable,
}

pub fn solve(program: &GroundProgram) -> SolveResult {
    let translation = translate::translate(program);

    if translation.num_atoms == 0 {
        return SolveResult::Satisfiable(vec![]);
    }

    let mut assignment = Assignment::new(translation.num_atoms);
    let mut clause_db = ClauseDB::new(translation.num_atoms);
    let mut vsids = VsidsHeap::new(translation.num_atoms);
    let mut restarts = RestartPolicy::new(100);
    let mut ufs_checker = UnfoundedSetChecker::new(program, &translation.choice_atoms);
    let mut conflicts = 0u64;

    // Add all initial clauses
    for clause_lits in &translation.clauses {
        match clause_lits.len() {
            0 => return SolveResult::Unsatisfiable,
            1 => {
                let lit = clause_lits[0];
                match assignment.value_lit(lit) {
                    LBool::True => {}
                    LBool::False => return SolveResult::Unsatisfiable,
                    LBool::Undef => assignment.assign(lit, 0, None),
                }
            }
            _ => {
                clause_db.add_clause(clause_lits.clone(), false);
            }
        }
    }

    if propagate::propagate(&mut clause_db, &mut assignment).is_some() {
        return SolveResult::Unsatisfiable;
    }

    loop {
        match propagate::propagate(&mut clause_db, &mut assignment) {
            Some(conflict) => {
                conflicts += 1;
                if assignment.decision_level() == 0 {
                    return SolveResult::Unsatisfiable;
                }
                let (learned, bt_level) = analyze::analyze(&clause_db, &assignment, conflict);

                for lit in &learned {
                    vsids.bump(lit.atom);
                }
                vsids.decay();

                let unassigned = assignment.backtrack_to(bt_level);
                for atom in unassigned {
                    vsids.insert(atom);
                }

                if learned.len() == 1 {
                    assignment.assign(learned[0], 0, None);
                } else {
                    let cidx = clause_db.add_clause(learned.clone(), true);
                    assignment.assign(learned[0], bt_level, Some(cidx));
                }

                clause_db.decay_activities();

                if restarts.should_restart(conflicts) {
                    let unassigned = assignment.backtrack_to(0);
                    for atom in unassigned {
                        vsids.insert(atom);
                    }
                    restarts.advance();

                    // Reduce learned clauses periodically at restart
                    if clause_db.should_reduce() {
                        clause_db.reduce_learnt(&assignment);
                    }
                }
            }
            None => {
                let loop_nogoods = ufs_checker.check(&assignment);
                if !loop_nogoods.is_empty() {
                    let mut added_any = false;
                    for nogood in loop_nogoods {
                        match nogood.len() {
                            0 => return SolveResult::Unsatisfiable,
                            1 => {
                                let lit = nogood[0];
                                if assignment.value_lit(lit) == LBool::Undef {
                                    assignment.assign(lit, assignment.decision_level(), None);
                                    added_any = true;
                                } else if assignment.value_lit(lit) == LBool::False {
                                    if assignment.decision_level() == 0 {
                                        return SolveResult::Unsatisfiable;
                                    }
                                    let unassigned = assignment.backtrack_to(0);
                                    for atom in unassigned {
                                        vsids.insert(atom);
                                    }
                                    assignment.assign(lit, 0, None);
                                    added_any = true;
                                }
                            }
                            _ => {
                                clause_db.add_clause(nogood, true);
                                added_any = true;
                            }
                        }
                    }
                    if added_any { continue; }
                }

                match vsids.pick(&assignment) {
                    Some(atom) => {
                        assignment.new_decision_level();
                        let polarity = assignment.saved_polarity(atom);
                        let lit = if polarity { Lit::pos(atom) } else { Lit::neg(atom) };
                        assignment.assign(lit, assignment.decision_level(), None);
                    }
                    None => {
                        let model: Vec<AtomId> = (0..translation.num_atoms)
                            .filter(|&i| assignment.value(AtomId(i)) == LBool::True)
                            .map(AtomId)
                            .collect();
                        return SolveResult::Satisfiable(model);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ground::program::{AtomTable, GroundAtom, GroundRule, RuleHead};
    use crate::types::SymbolId;

    fn make_program(rules: Vec<GroundRule>, num_atoms: usize) -> GroundProgram {
        let mut at = AtomTable::new();
        for i in 0..num_atoms {
            at.get_or_insert(GroundAtom { predicate: SymbolId(i as u32), args: vec![] });
        }
        GroundProgram { atom_table: at, rules, show_atoms: vec![], show_all: true }
    }

    #[test]
    fn empty_program() {
        let prog = make_program(vec![], 0);
        assert!(matches!(solve(&prog), SolveResult::Satisfiable(v) if v.is_empty()));
    }

    #[test]
    fn single_fact() {
        let a = AtomId(0);
        let prog = make_program(
            vec![GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] }],
            1,
        );
        match solve(&prog) {
            SolveResult::Satisfiable(model) => assert!(model.contains(&a)),
            SolveResult::Unsatisfiable => panic!("expected SAT"),
        }
    }

    #[test]
    fn simple_constraint_unsat() {
        let a = AtomId(0);
        let prog = make_program(
            vec![
                GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] },
                GroundRule { head: RuleHead::Constraint, body_pos: vec![a], body_neg: vec![] },
            ],
            1,
        );
        assert!(matches!(solve(&prog), SolveResult::Unsatisfiable));
    }

    #[test]
    fn rule_derivation() {
        let a = AtomId(0);
        let b = AtomId(1);
        let prog = make_program(
            vec![
                GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] },
                GroundRule { head: RuleHead::Normal(b), body_pos: vec![a], body_neg: vec![] },
            ],
            2,
        );
        match solve(&prog) {
            SolveResult::Satisfiable(model) => {
                assert!(model.contains(&a));
                assert!(model.contains(&b));
            }
            SolveResult::Unsatisfiable => panic!("expected SAT"),
        }
    }

    #[test]
    fn choice_rule() {
        let a = AtomId(0);
        let prog = make_program(
            vec![GroundRule { head: RuleHead::Choice(vec![a]), body_pos: vec![], body_neg: vec![] }],
            1,
        );
        assert!(matches!(solve(&prog), SolveResult::Satisfiable(_)));
    }

    #[test]
    fn self_supporting_loop_unsat() {
        let a = AtomId(0);
        let prog = make_program(
            vec![GroundRule { head: RuleHead::Normal(a), body_pos: vec![a], body_neg: vec![] }],
            1,
        );
        match solve(&prog) {
            SolveResult::Satisfiable(model) => assert!(!model.contains(&a)),
            SolveResult::Unsatisfiable => panic!("expected SAT with empty model"),
        }
    }

    #[test]
    fn negation_as_failure() {
        let a = AtomId(0);
        let b = AtomId(1);
        let prog = make_program(
            vec![GroundRule { head: RuleHead::Normal(b), body_pos: vec![], body_neg: vec![a] }],
            2,
        );
        match solve(&prog) {
            SolveResult::Satisfiable(model) => {
                assert!(!model.contains(&a));
                assert!(model.contains(&b));
            }
            SolveResult::Unsatisfiable => panic!("expected SAT"),
        }
    }
}
