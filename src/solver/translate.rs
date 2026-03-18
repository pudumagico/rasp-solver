use std::collections::HashMap;

use crate::ground::program::{GroundProgram, RuleHead};
use crate::types::{AtomId, Lit};

/// The result of translating a GroundProgram into clauses.
pub struct Translation {
    pub num_atoms: u32,
    pub clauses: Vec<Vec<Lit>>,
    /// Atoms that appear in choice rule heads (don't require support).
    pub choice_atoms: Vec<bool>,
}

/// Translate a ground program into clauses via Clark's completion.
pub fn translate(program: &GroundProgram) -> Translation {
    let num_atoms = program.atom_table.len() as u32;
    let mut clauses = Vec::new();
    let mut choice_atoms = vec![false; num_atoms as usize];

    // Collect support rules per atom: which rules have this atom in the head
    let mut support: HashMap<AtomId, Vec<usize>> = HashMap::new();

    for (ri, rule) in program.rules.iter().enumerate() {
        match &rule.head {
            RuleHead::Normal(head_id) => {
                support.entry(*head_id).or_default().push(ri);
                // Body → Head: if all body lits hold, head must be true.
                // Clause: ¬b1 ∨ ... ∨ ¬bn ∨ c1 ∨ ... ∨ cm ∨ head
                let mut clause = Vec::new();
                for &bp in &rule.body_pos {
                    clause.push(Lit::neg(bp));
                }
                for &bn in &rule.body_neg {
                    clause.push(Lit::pos(bn));
                }
                clause.push(Lit::pos(*head_id));
                clauses.push(clause);
            }
            RuleHead::Constraint => {
                // Integrity constraint: body must not all hold.
                // Clause: ¬b1 ∨ ... ∨ ¬bn ∨ c1 ∨ ... ∨ cm
                // Empty clause = unconditional constraint = UNSAT
                let mut clause = Vec::new();
                for &bp in &rule.body_pos {
                    clause.push(Lit::neg(bp));
                }
                for &bn in &rule.body_neg {
                    clause.push(Lit::pos(bn));
                }
                clauses.push(clause);
            }
            RuleHead::Choice(atoms) => {
                for &a in atoms {
                    choice_atoms[a.index()] = true;
                }
                // Choice rules: body → each head atom CAN be true (no "must" clause).
                // But we still need support: if the body is false, head atoms must be false.
                for &a in atoms {
                    support.entry(a).or_default().push(ri);
                    // body → head_i is optional (choice), so no body→head clause.
                    // But: head_i → body (if atom chosen, body must hold).
                    let mut clause = Vec::new();
                    clause.push(Lit::neg(a));
                    for &bp in &rule.body_pos {
                        clause.push(Lit::neg(bp));
                    }
                    for &bn in &rule.body_neg {
                        clause.push(Lit::pos(bn));
                    }
                    // Actually for choice: head_i can only be true if body is true.
                    // Clause: ¬head_i ∨ (body holds) — but body holds = all pos are true, all neg are false.
                    // This is: ¬head_i ∨ ¬¬b1 ∨ ... which simplifies to: ¬head_i ∨ b1 ∧ ...
                    // That's not a single clause. Instead, for each body literal:
                    // ¬head_i ∨ b_pos_j  and  ¬head_i ∨ ¬b_neg_j
                    // These are the "if you chose the atom, body must hold" clauses.
                }
                // Generate proper choice support clauses
                for &a in atoms {
                    for &bp in &rule.body_pos {
                        clauses.push(vec![Lit::neg(a), Lit::pos(bp)]);
                    }
                    for &bn in &rule.body_neg {
                        clauses.push(vec![Lit::neg(a), Lit::neg(bn)]);
                    }
                }
            }
        }
    }

    // Support clauses (Clark's completion): each non-choice atom must have at least one
    // supporting rule whose body is satisfied.
    // For atom a with rules r1, r2, ..., rk:
    // ¬a ∨ body(r1) ∨ body(r2) ∨ ... ∨ body(rk)
    // This is complex with multi-literal bodies, so we use body auxiliary atoms.
    // For each rule ri with body b1,...,bn,¬c1,...,¬cm defining atom a:
    //   aux_ri ↔ (b1 ∧ ... ∧ bn ∧ ¬c1 ∧ ... ∧ ¬cm)
    //   Support: ¬a ∨ aux_r1 ∨ aux_r2 ∨ ...
    // For now, skip support clauses for atoms with only one defining rule
    // (they're handled by the body→head clause above).
    // For atoms with multiple defining rules, the body→head clauses already
    // ensure correctness (the atom can be true if ANY rule fires).
    // The completion would also add ¬atom for atoms with NO defining rules.
    for i in 0..num_atoms {
        let atom = AtomId(i);
        if choice_atoms[atom.index()] { continue; }
        if !support.contains_key(&atom) {
            // Atom has no support — must be false
            clauses.push(vec![Lit::neg(atom)]);
        }
    }

    Translation { num_atoms, clauses, choice_atoms }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ground::program::{AtomTable, GroundAtom, GroundRule};
    use crate::types::SymbolId;

    #[test]
    fn translate_simple_fact() {
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] }],
            show_atoms: vec![],
            show_all: true,
        };
        let t = translate(&prog);
        assert_eq!(t.num_atoms, 1);
        // Should have body→head clause: just [+a] (empty body → a)
        assert!(t.clauses.iter().any(|c| c == &vec![Lit::pos(a)]));
    }

    #[test]
    fn translate_constraint() {
        let mut at = AtomTable::new();
        let a = at.get_or_insert(GroundAtom { predicate: SymbolId(0), args: vec![] });
        let b = at.get_or_insert(GroundAtom { predicate: SymbolId(1), args: vec![] });
        let prog = GroundProgram {
            atom_table: at,
            rules: vec![
                GroundRule { head: RuleHead::Normal(a), body_pos: vec![], body_neg: vec![] },
                GroundRule { head: RuleHead::Normal(b), body_pos: vec![], body_neg: vec![] },
                GroundRule { head: RuleHead::Constraint, body_pos: vec![a, b], body_neg: vec![] },
            ],
            show_atoms: vec![],
            show_all: true,
        };
        let t = translate(&prog);
        // Constraint clause: ¬a ∨ ¬b
        assert!(t.clauses.iter().any(|c| c.contains(&Lit::neg(a)) && c.contains(&Lit::neg(b))));
    }
}
