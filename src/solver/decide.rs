use crate::types::AtomId;

use super::assignment::{Assignment, LBool};

/// VSIDS-style decision heuristic with binary max-heap.
pub struct VsidsHeap {
    activity: Vec<f64>,
    heap: Vec<u32>,           // atom indices in heap order
    position: Vec<Option<usize>>, // atom index → position in heap
    increment: f64,
    decay_factor: f64,
}

impl VsidsHeap {
    pub fn new(num_atoms: u32) -> Self {
        let n = num_atoms as usize;
        let heap: Vec<u32> = (0..n as u32).collect();
        let position: Vec<Option<usize>> = (0..n).map(Some).collect();
        Self {
            activity: vec![0.0; n],
            heap,
            position,
            increment: 1.0,
            decay_factor: 1.0 / 0.95,
        }
    }

    pub fn bump(&mut self, atom: AtomId) {
        let idx = atom.index();
        self.activity[idx] += self.increment;
        // Rescale if activity gets too large
        if self.activity[idx] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.increment *= 1e-100;
        }
        // Percolate up in heap
        if let Some(pos) = self.position[idx] {
            self.sift_up(pos);
        }
    }

    pub fn decay(&mut self) {
        self.increment *= self.decay_factor;
    }

    /// Pick the highest-activity unassigned atom.
    pub fn pick(&mut self, assignment: &Assignment) -> Option<AtomId> {
        while !self.heap.is_empty() {
            let top = self.heap[0];
            if assignment.value(AtomId(top)) == LBool::Undef {
                return Some(AtomId(top));
            }
            // Remove top (it's assigned)
            self.pop();
        }
        None
    }

    /// Re-insert an atom into the heap (after backtracking).
    pub fn insert(&mut self, atom: AtomId) {
        let idx = atom.index();
        if self.position[idx].is_some() { return; }
        let pos = self.heap.len();
        self.heap.push(idx as u32);
        self.position[idx] = Some(pos);
        self.sift_up(pos);
    }

    fn pop(&mut self) {
        let top = self.heap[0] as usize;
        self.position[top] = None;
        let last = self.heap.pop().unwrap();
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.position[last as usize] = Some(0);
            self.sift_down(0);
        }
    }

    fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            if self.activity[self.heap[pos] as usize] > self.activity[self.heap[parent] as usize] {
                self.heap.swap(pos, parent);
                self.position[self.heap[pos] as usize] = Some(pos);
                self.position[self.heap[parent] as usize] = Some(parent);
                pos = parent;
            } else {
                break;
            }
        }
    }

    fn sift_down(&mut self, mut pos: usize) {
        let len = self.heap.len();
        loop {
            let left = 2 * pos + 1;
            let right = 2 * pos + 2;
            let mut largest = pos;
            if left < len && self.activity[self.heap[left] as usize] > self.activity[self.heap[largest] as usize] {
                largest = left;
            }
            if right < len && self.activity[self.heap[right] as usize] > self.activity[self.heap[largest] as usize] {
                largest = right;
            }
            if largest == pos { break; }
            self.heap.swap(pos, largest);
            self.position[self.heap[pos] as usize] = Some(pos);
            self.position[self.heap[largest] as usize] = Some(largest);
            pos = largest;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pick_highest_activity() {
        let mut heap = VsidsHeap::new(3);
        let assignment = Assignment::new(3);
        heap.bump(AtomId(2));
        heap.bump(AtomId(2));
        heap.bump(AtomId(1));
        assert_eq!(heap.pick(&assignment), Some(AtomId(2)));
    }

    #[test]
    fn pick_skips_assigned() {
        let mut heap = VsidsHeap::new(3);
        let mut assignment = Assignment::new(3);
        heap.bump(AtomId(0));
        heap.bump(AtomId(0));
        assignment.assign(crate::types::Lit::pos(AtomId(0)), 0, None);
        let picked = heap.pick(&assignment);
        assert_ne!(picked, Some(AtomId(0)));
    }
}
