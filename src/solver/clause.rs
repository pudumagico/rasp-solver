use crate::types::Lit;

use super::assignment::{Assignment, LBool};

#[derive(Debug, Clone)]
pub struct ClauseHeader {
    pub start: u32,
    pub len: u16,
    pub learnt: bool,
    pub lbd: u32,
    pub activity: f32,
}

#[derive(Clone)]
struct Watch {
    clause_idx: u32,
    blocker: Lit,
}

pub struct ClauseDB {
    headers: Vec<ClauseHeader>,
    lit_arena: Vec<Lit>,
    watches: Vec<Vec<Watch>>,
    /// binary_imps[lit_index(p)] = (implied_lit, clause_idx) pairs
    binary_imps: Vec<Vec<(Lit, u32)>>,
    num_learnt: u32,
    max_learnt: u32,
}

/// Positive literal for atom i -> 2*i, negative -> 2*i+1
pub fn lit_index(lit: Lit) -> usize {
    let base = (lit.atom.0 as usize) * 2;
    if lit.positive { base } else { base + 1 }
}

impl ClauseDB {
    pub fn new(num_atoms: u32) -> Self {
        let n2 = (num_atoms as usize) * 2;
        Self {
            headers: Vec::new(),
            lit_arena: Vec::new(),
            watches: vec![Vec::new(); n2],
            binary_imps: vec![Vec::new(); n2],
            num_learnt: 0,
            max_learnt: num_atoms.max(100) * 3,
        }
    }

    pub fn num_clauses(&self) -> usize {
        self.headers.len()
    }

    pub fn clause_lits(&self, idx: u32) -> &[Lit] {
        let h = &self.headers[idx as usize];
        &self.lit_arena[h.start as usize..(h.start as usize + h.len as usize)]
    }

    fn clause_lits_mut(&mut self, idx: u32) -> &mut [Lit] {
        let h = &self.headers[idx as usize];
        &mut self.lit_arena[h.start as usize..(h.start as usize + h.len as usize)]
    }

    pub fn clause_header(&self, idx: u32) -> &ClauseHeader {
        &self.headers[idx as usize]
    }

    pub fn add_clause(&mut self, lits: Vec<Lit>, learnt: bool) -> u32 {
        self.add_clause_with_lbd(lits, learnt, 0)
    }

    pub fn add_clause_with_lbd(&mut self, lits: Vec<Lit>, learnt: bool, lbd: u32) -> u32 {
        if lits.len() == 2 {
            let idx = self.headers.len() as u32;
            // Store as binary implication: (a | b) means ~a => b and ~b => a
            self.binary_imps[lit_index(lits[0].negate())].push((lits[1], idx));
            self.binary_imps[lit_index(lits[1].negate())].push((lits[0], idx));
            if learnt { self.num_learnt += 1; }
            let start = self.lit_arena.len() as u32;
            self.lit_arena.extend_from_slice(&lits);
            self.headers.push(ClauseHeader { start, len: 2, learnt, lbd, activity: 0.0 });
            return idx;
        }
        let idx = self.headers.len() as u32;
        let start = self.lit_arena.len() as u32;
        let len = lits.len() as u16;
        if lits.len() >= 2 {
            let w0_idx = lit_index(lits[0].negate());
            let w1_idx = lit_index(lits[1].negate());
            self.watches[w0_idx].push(Watch { clause_idx: idx, blocker: lits[1] });
            self.watches[w1_idx].push(Watch { clause_idx: idx, blocker: lits[0] });
        }
        self.lit_arena.extend_from_slice(&lits);
        if learnt { self.num_learnt += 1; }
        self.headers.push(ClauseHeader { start, len, learnt, lbd, activity: 0.0 });
        idx
    }

    pub fn bump_activity(&mut self, idx: u32) {
        self.headers[idx as usize].activity += 1.0;
    }

    pub fn decay_activities(&mut self) {
        for h in &mut self.headers {
            h.activity *= 0.999;
        }
    }

    pub fn should_reduce(&self) -> bool {
        self.num_learnt > self.max_learnt
    }

    /// LBD-based clause reduction: protect glue clauses (LBD <= 2) and reason clauses.
    /// Sort remaining by LBD ascending, then activity descending. Delete worst 50%.
    pub fn reduce_learnt(&mut self, assignment: &Assignment) {
        let mut protected = vec![false; self.headers.len()];
        for &atom in assignment.trail() {
            if let Some(reason) = assignment.reason(atom)
                && (reason as usize) < protected.len()
            {
                protected[reason as usize] = true;
            }
        }

        let mut learnt_indices: Vec<usize> = (0..self.headers.len())
            .filter(|&i| {
                let h = &self.headers[i];
                h.learnt && !protected[i] && h.lbd > 2 && h.len > 0
            })
            .collect();

        // Sort by LBD ascending, then activity descending (worst = high LBD, low activity last)
        learnt_indices.sort_by(|&a, &b| {
            let ha = &self.headers[a];
            let hb = &self.headers[b];
            ha.lbd.cmp(&hb.lbd)
                .then(hb.activity.partial_cmp(&ha.activity).unwrap_or(std::cmp::Ordering::Equal))
        });

        let to_remove = learnt_indices.len() / 2;
        let remove_start = learnt_indices.len() - to_remove;
        let mut removed = vec![false; self.headers.len()];
        for &idx in &learnt_indices[remove_start..] {
            removed[idx] = true;
            self.headers[idx].len = 0;
            self.headers[idx].learnt = false;
            self.num_learnt -= 1;
        }

        for watch_list in &mut self.watches {
            watch_list.retain(|w| !removed[w.clause_idx as usize]);
        }

        self.max_learnt = (self.max_learnt as f64 * 1.1) as u32;
    }

    /// Binary propagation: when literal `p` becomes true, propagate all binary implications.
    /// Returns Some(clause_idx) on conflict (using u32::MAX as sentinel for binary conflict),
    /// or None if no conflict.
    pub fn propagate_binary(&self, p: Lit, assignment: &mut Assignment) -> Option<u32> {
        let idx = lit_index(p);
        for &(implied, clause_idx) in &self.binary_imps[idx] {
            match assignment.value_lit(implied) {
                LBool::True => {}
                LBool::False => return Some(clause_idx),
                LBool::Undef => {
                    assignment.assign(implied, assignment.decision_level(), Some(clause_idx));
                }
            }
        }
        None
    }

    pub fn propagate_literal(&mut self, p: Lit, assignment: &mut Assignment) -> Option<u32> {
        let false_lit = p.negate();
        let watch_idx = lit_index(p);

        let mut watchers = std::mem::take(&mut self.watches[watch_idx]);
        let mut i = 0;
        let mut conflict = None;

        while i < watchers.len() {
            if assignment.value_lit(watchers[i].blocker) == LBool::True {
                i += 1;
                continue;
            }

            let ci = watchers[i].clause_idx;
            let lits = self.clause_lits_mut(ci);

            if lits[0] == false_lit {
                lits.swap(0, 1);
            }

            if assignment.value_lit(lits[0]) == LBool::True {
                watchers[i].blocker = lits[0];
                i += 1;
                continue;
            }

            let mut found_new = false;
            let h = &self.headers[ci as usize];
            let clause_start = h.start as usize;
            let clause_len = h.len as usize;
            for k in 2..clause_len {
                if assignment.value_lit(self.lit_arena[clause_start + k]) != LBool::False {
                    self.lit_arena.swap(clause_start + 1, clause_start + k);
                    let new_watch_lit = self.lit_arena[clause_start + 1];
                    let new_watch_idx = lit_index(new_watch_lit.negate());
                    self.watches[new_watch_idx].push(Watch {
                        clause_idx: ci,
                        blocker: self.lit_arena[clause_start],
                    });
                    watchers.swap_remove(i);
                    found_new = true;
                    break;
                }
            }
            if found_new { continue; }

            let first = self.lit_arena[clause_start];
            if assignment.value_lit(first) == LBool::False {
                conflict = Some(ci);
                i += 1;
                break;
            }
            assignment.assign(first, assignment.decision_level(), Some(ci));
            i += 1;
        }

        // Remaining watchers stay
        while i < watchers.len() { i += 1; }
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
        let lits = vec![Lit::pos(AtomId(0)), Lit::neg(AtomId(1)), Lit::pos(AtomId(2))];
        let idx = db.add_clause(lits.clone(), false);
        assert_eq!(db.clause_lits(idx), &lits[..]);
    }

    #[test]
    fn binary_clause_stored_as_implication() {
        let mut db = ClauseDB::new(3);
        let lits = vec![Lit::pos(AtomId(0)), Lit::pos(AtomId(1))];
        let _idx = db.add_clause(lits, false);
        // ~a => b: binary_imps[lit_index(neg(a))] should contain pos(b)
        assert!(db.binary_imps[lit_index(Lit::neg(AtomId(0)))].iter().any(|(l, _)| *l == Lit::pos(AtomId(1))));
        assert!(db.binary_imps[lit_index(Lit::neg(AtomId(1)))].iter().any(|(l, _)| *l == Lit::pos(AtomId(0))));
    }

    #[test]
    fn unit_propagation_non_binary() {
        let mut db = ClauseDB::new(3);
        let mut assignment = Assignment::new(3);
        // Clause: a | b | c (3 lits, goes through watched literals)
        db.add_clause(vec![Lit::pos(AtomId(0)), Lit::pos(AtomId(1)), Lit::pos(AtomId(2))], false);
        assignment.assign(Lit::neg(AtomId(0)), 0, None);
        let conflict = db.propagate_literal(Lit::neg(AtomId(0)), &mut assignment);
        assert!(conflict.is_none());
        // b or c should not yet be propagated (both still undef, clause not unit)
        assignment.assign(Lit::neg(AtomId(1)), 0, None);
        let conflict = db.propagate_literal(Lit::neg(AtomId(1)), &mut assignment);
        assert!(conflict.is_none());
        assert_eq!(assignment.value(AtomId(2)), LBool::True);
    }
}
