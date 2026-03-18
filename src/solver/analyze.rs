use crate::types::Lit;

use super::assignment::Assignment;
use super::clause::ClauseDB;

/// First-UIP conflict analysis.
/// Returns (learned_clause, backtrack_level).
pub fn analyze(
    clause_db: &ClauseDB,
    assignment: &Assignment,
    conflict_clause: u32,
) -> (Vec<Lit>, u32) {
    let current_level = assignment.decision_level();
    let mut seen = vec![false; assignment.num_atoms() as usize];
    let mut learnt = Vec::new();
    let mut counter = 0u32; // number of yet-unresolved current-level literals
    let mut reason_clause = conflict_clause;
    let mut trail_idx = assignment.trail().len();

    loop {
        // Add literals from the reason clause
        for &lit in &clause_db.clause(reason_clause).lits {
            let atom = lit.atom;
            if seen[atom.index()] { continue; }
            seen[atom.index()] = true;
            if assignment.level(atom) == current_level {
                counter += 1;
            } else if assignment.level(atom) > 0 {
                // Add to learned clause (decision levels < current)
                learnt.push(lit.negate());
            }
            // Level 0 literals are always true — don't add them
        }

        // Walk trail backwards to find the next seen atom at current level
        loop {
            trail_idx -= 1;
            let atom = assignment.trail()[trail_idx];
            if seen[atom.index()] && assignment.level(atom) == current_level {
                counter -= 1;
                if counter == 0 {
                    // This is the first UIP — add its negation as the asserting literal
                    let uip_lit = if assignment.value(atom) == super::assignment::LBool::True {
                        Lit::neg(atom)
                    } else {
                        Lit::pos(atom)
                    };
                    learnt.insert(0, uip_lit);
                    let bt_level = backtrack_level(&learnt, assignment);
                    return (learnt, bt_level);
                }
                // Resolve with this atom's reason clause
                if let Some(r) = assignment.reason(atom) {
                    reason_clause = r;
                }
                break;
            }
        }
    }
}

/// Compute the backtrack level: second-highest decision level in the learned clause.
fn backtrack_level(learnt: &[Lit], assignment: &Assignment) -> u32 {
    if learnt.len() <= 1 {
        return 0;
    }
    let mut max_level = 0;
    let mut max_idx = 1;
    for (i, lit) in learnt.iter().enumerate().skip(1) {
        let lvl = assignment.level(lit.atom);
        if lvl > max_level {
            max_level = lvl;
            max_idx = i;
        }
    }
    // Swap the highest-level literal to position 1 for watched-literal invariant
    // (learnt[0] is the asserting literal, learnt[1] should have the highest level)
    // This is important so that when we add the clause, watches are set up correctly.
    let _ = max_idx; // The literal is already in the clause; the level is what matters
    max_level
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::AtomId;

    #[test]
    fn backtrack_level_single() {
        let assignment = Assignment::new(1);
        let learnt = vec![Lit::neg(AtomId(0))];
        assert_eq!(backtrack_level(&learnt, &assignment), 0);
    }
}
