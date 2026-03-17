use std::collections::HashMap;

use crate::types::{AtomId, SymbolId, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GroundAtom {
    pub predicate: SymbolId,
    pub args: Vec<Value>,
}

#[derive(Debug, Clone)]
pub struct GroundRule {
    pub head: RuleHead,
    pub body_pos: Vec<AtomId>,
    pub body_neg: Vec<AtomId>,
}

#[derive(Debug, Clone)]
pub enum RuleHead {
    Normal(AtomId),
    Choice(Vec<AtomId>),
    Constraint,
}

#[derive(Debug)]
pub struct GroundProgram {
    pub atom_table: AtomTable,
    pub rules: Vec<GroundRule>,
    pub show_atoms: Vec<AtomId>,
    pub show_all: bool,
}

#[derive(Debug, Default)]
pub struct AtomTable {
    atoms: Vec<GroundAtom>,
    index: HashMap<GroundAtom, AtomId>,
}

impl AtomTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get or create an AtomId for the given ground atom.
    pub fn get_or_insert(&mut self, atom: GroundAtom) -> AtomId {
        if let Some(&id) = self.index.get(&atom) {
            return id;
        }
        let id = AtomId(self.atoms.len() as u32);
        self.index.insert(atom.clone(), id);
        self.atoms.push(atom);
        id
    }

    pub fn get(&self, atom: &GroundAtom) -> Option<AtomId> {
        self.index.get(atom).copied()
    }

    pub fn resolve(&self, id: AtomId) -> &GroundAtom {
        &self.atoms[id.index()]
    }

    pub fn len(&self) -> usize {
        self.atoms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }
}
