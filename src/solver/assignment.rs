use crate::types::{AtomId, Lit};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

pub struct Assignment {
    values: Vec<LBool>,
    polarities: Vec<bool>,
    reasons: Vec<Option<u32>>,
    levels: Vec<u32>,
    trail: Vec<AtomId>,
    trail_lim: Vec<usize>,
    /// Index into trail: everything before this has been propagated.
    pub propagation_head: usize,
}

impl Assignment {
    pub fn new(num_atoms: u32) -> Self {
        let n = num_atoms as usize;
        Self {
            values: vec![LBool::Undef; n],
            polarities: vec![false; n],
            reasons: vec![None; n],
            levels: vec![0; n],
            trail: Vec::with_capacity(n),
            trail_lim: Vec::new(),
            propagation_head: 0,
        }
    }

    pub fn value(&self, atom: AtomId) -> LBool {
        self.values[atom.index()]
    }

    pub fn value_lit(&self, lit: Lit) -> LBool {
        let v = self.values[lit.atom.index()];
        match (v, lit.positive) {
            (LBool::True, true) | (LBool::False, false) => LBool::True,
            (LBool::False, true) | (LBool::True, false) => LBool::False,
            (LBool::Undef, _) => LBool::Undef,
        }
    }

    pub fn assign(&mut self, lit: Lit, level: u32, reason: Option<u32>) {
        let idx = lit.atom.index();
        self.values[idx] = if lit.positive { LBool::True } else { LBool::False };
        self.polarities[idx] = lit.positive;
        self.reasons[idx] = reason;
        self.levels[idx] = level;
        self.trail.push(lit.atom);
    }

    pub fn reason(&self, atom: AtomId) -> Option<u32> {
        self.reasons[atom.index()]
    }

    pub fn level(&self, atom: AtomId) -> u32 {
        self.levels[atom.index()]
    }

    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    pub fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    /// Backtrack to the given decision level, returning the atoms that were unassigned.
    pub fn backtrack_to(&mut self, level: u32) -> Vec<AtomId> {
        let target = level as usize;
        let mut unassigned = Vec::new();
        while self.trail_lim.len() > target {
            let start = self.trail_lim.pop().unwrap();
            for i in start..self.trail.len() {
                let atom = self.trail[i];
                self.values[atom.index()] = LBool::Undef;
                unassigned.push(atom);
            }
            self.trail.truncate(start);
        }
        self.propagation_head = self.trail.len();
        unassigned
    }

    pub fn trail(&self) -> &[AtomId] {
        &self.trail
    }

    pub fn saved_polarity(&self, atom: AtomId) -> bool {
        self.polarities[atom.index()]
    }

    pub fn num_atoms(&self) -> u32 {
        self.values.len() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_and_backtrack() {
        let mut a = Assignment::new(3);
        a.new_decision_level();
        a.assign(Lit::pos(AtomId(0)), 1, None);
        assert_eq!(a.value(AtomId(0)), LBool::True);
        assert_eq!(a.decision_level(), 1);
        a.backtrack_to(0);
        assert_eq!(a.value(AtomId(0)), LBool::Undef);
        assert_eq!(a.decision_level(), 0);
    }

    #[test]
    fn value_lit_polarity() {
        let mut a = Assignment::new(2);
        a.assign(Lit::pos(AtomId(0)), 0, None);
        a.assign(Lit::neg(AtomId(1)), 0, None);
        assert_eq!(a.value_lit(Lit::pos(AtomId(0))), LBool::True);
        assert_eq!(a.value_lit(Lit::neg(AtomId(0))), LBool::False);
        assert_eq!(a.value_lit(Lit::neg(AtomId(1))), LBool::True);
        assert_eq!(a.value_lit(Lit::pos(AtomId(1))), LBool::False);
    }
}
