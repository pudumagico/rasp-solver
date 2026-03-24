use crate::types::{AtomId, Lit};

use super::assignment::Assignment;
use super::clause::ClauseDB;

/// First-UIP conflict analysis.
/// Returns (learned_clause, backtrack_level, lbd).
/// Collects all atoms seen during resolution into `seen_atoms` for reason-side VSIDS bumping.
pub fn analyze(
    clause_db: &ClauseDB,
    assignment: &Assignment,
    conflict_clause: u32,
    seen_atoms: &mut Vec<AtomId>,
) -> (Vec<Lit>, u32, u32) {
    let current_level = assignment.decision_level();
    let n = assignment.num_atoms() as usize;
    let mut seen = vec![false; n];
    let mut learnt = Vec::new();
    let mut counter = 0u32;
    let mut reason_clause = conflict_clause;
    let mut trail_idx = assignment.trail().len();

    loop {
        for &lit in clause_db.clause_lits(reason_clause) {
            let atom = lit.atom;
            if seen[atom.index()] { continue; }
            seen[atom.index()] = true;
            seen_atoms.push(atom);
            if assignment.level(atom) == current_level {
                counter += 1;
            } else if assignment.level(atom) > 0 {
                learnt.push(lit.negate());
            }
        }

        loop {
            trail_idx -= 1;
            let atom = assignment.trail()[trail_idx];
            if seen[atom.index()] && assignment.level(atom) == current_level {
                counter -= 1;
                if counter == 0 {
                    let uip_lit = if assignment.value(atom) == super::assignment::LBool::True {
                        Lit::neg(atom)
                    } else {
                        Lit::pos(atom)
                    };
                    learnt.insert(0, uip_lit);
                    minimize_clause(&mut learnt, &seen, clause_db, assignment, n);
                    let bt_level = backtrack_level(&mut learnt, assignment);
                    let lbd = compute_lbd(&learnt, assignment, n);
                    return (learnt, bt_level, lbd);
                }
                if let Some(r) = assignment.reason(atom) {
                    reason_clause = r;
                }
                break;
            }
        }
    }
}

fn compute_lbd(learnt: &[Lit], assignment: &Assignment, num_atoms: usize) -> u32 {
    let mut stamp = vec![false; num_atoms + 1];
    let mut count = 0u32;
    for lit in learnt {
        let lvl = assignment.level(lit.atom) as usize;
        if lvl > 0 && !stamp[lvl] {
            stamp[lvl] = true;
            count += 1;
        }
    }
    count.max(1)
}

/// Swap highest-level literal to position 1 for watched-literal invariant.
fn backtrack_level(learnt: &mut [Lit], assignment: &Assignment) -> u32 {
    if learnt.len() <= 1 { return 0; }
    let mut max_level = 0;
    let mut max_idx = 1;
    for (i, lit) in learnt.iter().enumerate().skip(1) {
        let lvl = assignment.level(lit.atom);
        if lvl > max_level {
            max_level = lvl;
            max_idx = i;
        }
    }
    learnt.swap(1, max_idx);
    max_level
}

/// Recursive clause minimization: remove literals whose reason is subsumed by the learned clause.
fn minimize_clause(
    learnt: &mut Vec<Lit>,
    seen: &[bool],
    clause_db: &ClauseDB,
    assignment: &Assignment,
    num_atoms: usize,
) {
    let mut level_present = vec![false; num_atoms + 1];
    for lit in learnt.iter() {
        level_present[assignment.level(lit.atom) as usize] = true;
    }
    let mut visited = vec![false; num_atoms];
    let mut removable = vec![false; learnt.len()];
    for i in 1..learnt.len() {
        // Reset visited for each candidate
        visited.iter_mut().for_each(|v| *v = false);
        removable[i] = lit_redundant(learnt[i].negate(), seen, &level_present, clause_db, assignment, &mut visited, 0);
    }
    let mut j = 1;
    for i in 1..learnt.len() {
        if !removable[i] {
            learnt[j] = learnt[i];
            j += 1;
        }
    }
    learnt.truncate(j);
}

fn lit_redundant(
    lit: Lit,
    seen: &[bool],
    level_present: &[bool],
    clause_db: &ClauseDB,
    assignment: &Assignment,
    visited: &mut Vec<bool>,
    depth: u32,
) -> bool {
    if depth > 100 { return false; }
    let reason = match assignment.reason(lit.atom) {
        Some(r) => r,
        None => return false,
    };
    for &r_lit in clause_db.clause_lits(reason) {
        if r_lit.atom == lit.atom { continue; }
        let lvl = assignment.level(r_lit.atom);
        if lvl == 0 { continue; }
        if seen[r_lit.atom.index()] { continue; }
        if !level_present[lvl as usize] { return false; }
        if visited[r_lit.atom.index()] { continue; }
        visited[r_lit.atom.index()] = true;
        if !lit_redundant(r_lit, seen, level_present, clause_db, assignment, visited, depth + 1) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::AtomId;

    #[test]
    fn backtrack_level_single() {
        let assignment = Assignment::new(1);
        let mut learnt = vec![Lit::neg(AtomId(0))];
        assert_eq!(backtrack_level(&mut learnt, &assignment), 0);
    }
}
