/// Interned symbol identifier (predicate names, constants).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

/// Unique identifier for a ground atom in the atom table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AtomId(pub u32);

/// A ground value: integer or interned symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Value {
    Int(i64),
    Sym(SymbolId),
}

/// A signed literal: an atom with polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit {
    pub atom: AtomId,
    pub positive: bool,
}

impl Lit {
    pub fn pos(atom: AtomId) -> Self {
        Self { atom, positive: true }
    }

    pub fn neg(atom: AtomId) -> Self {
        Self { atom, positive: false }
    }

    pub fn negate(self) -> Self {
        Self { atom: self.atom, positive: !self.positive }
    }
}

impl AtomId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl SymbolId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lit_pos_neg() {
        let a = AtomId(0);
        let p = Lit::pos(a);
        let n = Lit::neg(a);
        assert!(p.positive);
        assert!(!n.positive);
        assert_eq!(p.atom, a);
        assert_eq!(n.atom, a);
    }

    #[test]
    fn lit_negate() {
        let lit = Lit::pos(AtomId(1));
        let neg = lit.negate();
        assert!(!neg.positive);
        assert_eq!(neg.negate(), lit);
    }

    #[test]
    fn atom_symbol_index() {
        assert_eq!(AtomId(42).index(), 42);
        assert_eq!(SymbolId(7).index(), 7);
    }
}
