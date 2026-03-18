use crate::ground::program::{GroundProgram, RuleHead};
use crate::types::{AtomId, Lit};

use super::assignment::{Assignment, LBool};

/// Source-pointer based unfounded set detection.
///
/// Detects atoms that are true but have no external support (i.e., all their
/// defining rules depend circularly on the atom itself or other unsupported atoms).
/// These atoms form an "unfounded set" and must be set to false for stable model semantics.
pub struct UnfoundedSetChecker {
    /// For each rule: positive body atoms.
    rule_body_pos: Vec<Vec<AtomId>>,
    /// For each rule: negative body atoms.
    rule_body_neg: Vec<Vec<AtomId>>,
    /// For each atom: which rules define it (have it in the head).
    defining_rules: Vec<Vec<usize>>,
    /// Atoms that are choice atoms (don't need support).
    choice_atoms: Vec<bool>,
    num_atoms: u32,
}

impl UnfoundedSetChecker {
    pub fn new(program: &GroundProgram, choice_atoms: &[bool]) -> Self {
        let num_atoms = program.atom_table.len() as u32;
        let n = num_atoms as usize;
        let mut rule_body_pos = Vec::new();
        let mut rule_body_neg = Vec::new();
        let mut defining_rules: Vec<Vec<usize>> = vec![Vec::new(); n];

        for (ri, rule) in program.rules.iter().enumerate() {
            let heads: Vec<AtomId> = match &rule.head {
                RuleHead::Normal(a) => vec![*a],
                RuleHead::Disjunction(atoms) | RuleHead::Choice(atoms) => atoms.clone(),
                RuleHead::Constraint => vec![],
            };
            for &h in &heads {
                if (h.0 as usize) < n {
                    defining_rules[h.index()].push(ri);
                }
            }
            rule_body_pos.push(rule.body_pos.clone());
            rule_body_neg.push(rule.body_neg.clone());
        }

        Self { rule_body_pos, rule_body_neg, defining_rules, choice_atoms: choice_atoms.to_vec(), num_atoms }
    }

    /// Compute the greatest unfounded set and return loop nogoods.
    ///
    /// Algorithm:
    /// 1. Start with U = all true non-choice atoms
    /// 2. Remove atoms that have a defining rule whose positive body is entirely outside U
    ///    and whose body is satisfiable under the current assignment
    /// 3. Repeat until fixpoint. Remaining atoms in U are unfounded.
    pub fn check(&mut self, assignment: &Assignment) -> Vec<Vec<Lit>> {
        let n = self.num_atoms as usize;
        let mut in_u = vec![false; n];
        for i in 0..self.num_atoms {
            let atom = AtomId(i);
            if !self.choice_atoms[atom.index()] && assignment.value(atom) == LBool::True {
                in_u[atom.index()] = true;
            }
        }

        // Fixpoint: remove atoms with external support
        let mut changed = true;
        while changed {
            changed = false;
            for i in 0..self.num_atoms {
                let atom = AtomId(i);
                if !in_u[atom.index()] { continue; }
                let has_external = self.defining_rules[atom.index()].iter().any(|&ri| {
                    self.rule_body_satisfiable(ri, assignment)
                        && self.rule_body_pos[ri].iter().all(|&bp| !in_u[bp.index()])
                });
                if has_external {
                    in_u[atom.index()] = false;
                    changed = true;
                }
            }
        }

        let mut nogoods = Vec::new();
        for i in 0..self.num_atoms {
            if in_u[i as usize] {
                nogoods.push(vec![Lit::neg(AtomId(i))]);
            }
        }
        nogoods
    }

    fn rule_body_satisfiable(&self, rule_idx: usize, assignment: &Assignment) -> bool {
        for &bp in &self.rule_body_pos[rule_idx] {
            if assignment.value(bp) == LBool::False { return false; }
        }
        for &bn in &self.rule_body_neg[rule_idx] {
            if assignment.value(bn) == LBool::True { return false; }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ground::program::{AtomTable, GroundAtom, GroundRule};
    use crate::types::SymbolId;

    #[test]
    fn no_unfounded_for_facts() {
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] }],
            show_atoms: vec![],
            show_all: true,
        };
        let mut checker = UnfoundedSetChecker::new(&prog, &[false]);
        let mut assignment = Assignment::new(1);
        assignment.assign(Lit::pos(a), 0, None);
        assert!(checker.check(&assignment).is_empty());
    }

    #[test]
    fn detects_self_supporting_loop() {
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![GroundRule { head: RuleHead::Normal(a), body_pos: vec![a], body_neg: vec![] }],
            show_atoms: vec![],
            show_all: true,
        };
        let mut checker = UnfoundedSetChecker::new(&prog, &[false]);
        let mut assignment = Assignment::new(1);
        assignment.assign(Lit::pos(a), 0, None);
        let nogoods = checker.check(&assignment);
        assert!(!nogoods.is_empty());
        assert!(nogoods[0].contains(&Lit::neg(a)));
    }

    #[test]
    fn choice_atoms_not_unfounded() {
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![GroundRule { head: RuleHead::Choice(vec![a]), body_pos: vec![], body_neg: vec![] }],
            show_atoms: vec![],
            show_all: true,
        };
        let mut checker = UnfoundedSetChecker::new(&prog, &[true]);
        let mut assignment = Assignment::new(1);
        assignment.assign(Lit::pos(a), 0, None);
        assert!(checker.check(&assignment).is_empty());
    }

    #[test]
    fn mutual_support_is_unfounded() {
        // a :- b.  b :- a.  (mutual cycle with no external support)
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let b = at.get_or_insert(GroundAtom { predicate: SymbolId(1), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![
                GroundRule { head: RuleHead::Normal(a), body_pos: vec![b], body_neg: vec![] },
                GroundRule { head: RuleHead::Normal(b), body_pos: vec![a], body_neg: vec![] },
            ],
            show_atoms: vec![],
            show_all: true,
        };
        let mut checker = UnfoundedSetChecker::new(&prog, &[false, false]);
        let mut assignment = Assignment::new(2);
        assignment.assign(Lit::pos(a), 0, None);
        assignment.assign(Lit::pos(b), 0, None);
        let nogoods = checker.check(&assignment);
        assert_eq!(nogoods.len(), 2); // both a and b are unfounded
    }
}
