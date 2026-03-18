use crate::types::Lit;

use super::assignment::{Assignment, LBool};

#[derive(Debug, Clone)]
pub struct Clause {
    pub lits: Vec<Lit>,
    pub learnt: bool,
    pub activity: f64,
}

#[derive(Clone)]
struct Watch {
    clause_idx: u32,
    blocker: Lit,
}

pub struct ClauseDB {
    clauses: Vec<Clause>,
    watches: Vec<Vec<Watch>>, // watches[lit_index] = watchers of that literal
    num_learnt: u32,
    max_learnt: u32,
}

/// Convert a literal to an index for the watch lists.
/// Positive literal for atom i → 2*i, negative → 2*i+1.
fn lit_index(lit: Lit) -> usize {
    let base = (lit.atom.0 as usize) * 2;
    if lit.positive { base } else { base + 1 }
}

impl ClauseDB {
    pub fn new(num_atoms: u32) -> Self {
        Self {
            clauses: Vec::new(),
            watches: vec![Vec::new(); (num_atoms as usize) * 2],
            num_learnt: 0,
            max_learnt: num_atoms.max(100) * 3,
        }
    }

    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub fn clause(&self, idx: u32) -> &Clause {
        &self.clauses[idx as usize]
    }

    /// Add a clause. Returns the clause index.
    /// If the clause is unit or empty under current assignment, caller must handle.
    pub fn add_clause(&mut self, lits: Vec<Lit>, learnt: bool) -> u32 {
        let idx = self.clauses.len() as u32;
        if lits.len() >= 2 {
            // Watch the first two literals
            let w0_idx = lit_index(lits[0].negate());
            let w1_idx = lit_index(lits[1].negate());
            self.watches[w0_idx].push(Watch { clause_idx: idx, blocker: lits[1] });
            self.watches[w1_idx].push(Watch { clause_idx: idx, blocker: lits[0] });
        }
        if learnt { self.num_learnt += 1; }
        self.clauses.push(Clause { lits, learnt, activity: 0.0 });
        idx
    }

    /// Bump activity for a clause (called during conflict analysis).
    pub fn bump_activity(&mut self, idx: u32) {
        self.clauses[idx as usize].activity += 1.0;
    }

    /// Decay all clause activities.
    pub fn decay_activities(&mut self) {
        for c in &mut self.clauses {
            c.activity *= 0.999;
        }
    }

    /// Returns true if a learned clause reduction should be performed.
    pub fn should_reduce(&self) -> bool {
        self.num_learnt > self.max_learnt
    }

    /// Remove half of the lowest-activity learned clauses.
    /// Clauses used as reasons on the current trail are protected.
    pub fn reduce_learnt(&mut self, assignment: &Assignment) {
        // Collect reason clause indices (protected from deletion)
        let mut protected = vec![false; self.clauses.len()];
        for &atom in assignment.trail() {
            if let Some(reason) = assignment.reason(atom) {
                protected[reason as usize] = true;
            }
        }

        // Sort learned clauses by activity, mark bottom half for deletion
        let mut learnt_indices: Vec<usize> = (0..self.clauses.len())
            .filter(|&i| self.clauses[i].learnt && !protected[i])
            .collect();
        learnt_indices.sort_by(|&a, &b| {
            self.clauses[a].activity.partial_cmp(&self.clauses[b].activity).unwrap()
        });

        let to_remove = learnt_indices.len() / 2;
        let mut removed = vec![false; self.clauses.len()];
        for &idx in &learnt_indices[..to_remove] {
            removed[idx] = true;
            self.clauses[idx].lits.clear(); // mark as empty (effectively deleted)
            self.clauses[idx].learnt = false;
            self.num_learnt -= 1;
        }

        // Clean up watch lists: remove watches pointing to deleted clauses
        for watch_list in &mut self.watches {
            watch_list.retain(|w| !removed[w.clause_idx as usize]);
        }

        self.max_learnt = (self.max_learnt as f64 * 1.1) as u32;
    }

    /// Propagate: a literal `p` has become true. Check all clauses watching `¬p`.
    /// Returns Some(clause_idx) on conflict, None otherwise.
    pub fn propagate_literal(&mut self, p: Lit, assignment: &mut Assignment) -> Option<u32> {
        // p just became true. Clauses watching ¬p (where p.negate() is a watched literal)
        // are stored at watches[lit_index(p)] (since add_clause stores at lit_index(lit.negate())).
        let false_lit = p.negate();
        let watch_idx = lit_index(p);

        // Swap out the watch list to avoid borrow issues
        let mut watchers = std::mem::take(&mut self.watches[watch_idx]);
        let mut i = 0;
        let mut conflict = None;

        while i < watchers.len() {
            // Quick check: if blocker is true, clause is satisfied
            if assignment.value_lit(watchers[i].blocker) == LBool::True {
                i += 1;
                continue;
            }

            let ci = watchers[i].clause_idx as usize;
            let clause_lits = &mut self.clauses[ci].lits;

            // Ensure the false literal is at position 1
            if clause_lits[0] == false_lit {
                clause_lits.swap(0, 1);
            }

            // If first literal is true, clause is satisfied — update blocker
            if assignment.value_lit(clause_lits[0]) == LBool::True {
                watchers[i].blocker = clause_lits[0];
                i += 1;
                continue;
            }

            // Look for a new literal to watch (not false, not position 0 or 1)
            let mut found_new = false;
            for k in 2..clause_lits.len() {
                if assignment.value_lit(clause_lits[k]) != LBool::False {
                    clause_lits.swap(1, k);
                    let new_watch_idx = lit_index(clause_lits[1].negate());
                    self.watches[new_watch_idx].push(Watch {
                        clause_idx: watchers[i].clause_idx,
                        blocker: clause_lits[0],
                    });
                    // Remove this watcher (swap-remove)
                    watchers.swap_remove(i);
                    found_new = true;
                    break;
                }
            }
            if found_new { continue; }

            // No new watch found. clause_lits[0] is the only non-false literal.
            if assignment.value_lit(clause_lits[0]) == LBool::False {
                // Conflict
                conflict = Some(watchers[i].clause_idx);
                i += 1;
                break;
            }
            // Unit propagation
            let unit_lit = clause_lits[0];
            assignment.assign(unit_lit, assignment.decision_level(), Some(watchers[i].clause_idx));
            i += 1;
        }

        // Move remaining watchers back
        while i < watchers.len() {
            i += 1;
        }
        self.watches[watch_idx] = watchers;
        conflict
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::AtomId;

    #[test]
    fn add_and_retrieve_clause() {
        let mut db = ClauseDB::new(3);
        let lits = vec![Lit::pos(AtomId(0)), Lit::neg(AtomId(1))];
        let idx = db.add_clause(lits.clone(), false);
        assert_eq!(db.clause(idx).lits, lits);
    }

    #[test]
    fn unit_propagation() {
        let mut db = ClauseDB::new(3);
        let mut assignment = Assignment::new(3);
        // Clause: a ∨ b (if ¬a, propagate b)
        db.add_clause(vec![Lit::pos(AtomId(0)), Lit::pos(AtomId(1))], false);
        // Assign ¬a
        assignment.assign(Lit::neg(AtomId(0)), 0, None);
        let conflict = db.propagate_literal(Lit::neg(AtomId(0)), &mut assignment);
        assert!(conflict.is_none());
        assert_eq!(assignment.value(AtomId(1)), LBool::True);
    }
}
