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
    Disjunction(Vec<AtomId>),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atom_table_insert_and_resolve() {
        let mut table = AtomTable::new();
        let atom = GroundAtom { predicate: SymbolId(0), args: vec![Value::Int(1)] };
        let id = table.get_or_insert(atom.clone());
        assert_eq!(table.resolve(id), &atom);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn atom_table_dedup() {
        let mut table = AtomTable::new();
        let atom = GroundAtom { predicate: SymbolId(0), args: vec![Value::Sym(SymbolId(1))] };
        let id1 = table.get_or_insert(atom.clone());
        let id2 = table.get_or_insert(atom.clone());
        assert_eq!(id1, id2);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn atom_table_get() {
        let mut table = AtomTable::new();
        let atom = GroundAtom { predicate: SymbolId(0), args: vec![] };
        assert_eq!(table.get(&atom), None);
        let id = table.get_or_insert(atom.clone());
        assert_eq!(table.get(&atom), Some(id));
    }
}
