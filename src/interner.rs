use std::collections::HashMap;

use crate::types::SymbolId;

/// Arena-based string interner. All predicate names and constants are interned
/// to u32 indices for fast comparison and hashing.
#[derive(Debug, Default)]
pub struct Interner {
    map: HashMap<String, SymbolId>,
    strings: Vec<String>,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a string, returning its unique SymbolId.
    /// Returns the existing id if already interned.
    pub fn intern(&mut self, s: &str) -> SymbolId {
        if let Some(&id) = self.map.get(s) {
            return id;
        }
        let id = SymbolId(self.strings.len() as u32);
        self.strings.push(s.to_owned());
        self.map.insert(s.to_owned(), id);
        id
    }

    /// Resolve a SymbolId back to its string.
    pub fn resolve(&self, id: SymbolId) -> &str {
        &self.strings[id.index()]
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_and_resolve() {
        let mut interner = Interner::new();
        let a = interner.intern("foo");
        let b = interner.intern("bar");
        let a2 = interner.intern("foo");
        assert_eq!(a, a2);
        assert_ne!(a, b);
        assert_eq!(interner.resolve(a), "foo");
        assert_eq!(interner.resolve(b), "bar");
        assert_eq!(interner.len(), 2);
    }
}
