use std::collections::{HashMap, HashSet};

use crate::parser::ast::{self, Statement, Term};
use crate::types::{SymbolId, Value};

/// Maps predicate/position → set of possible ground values.
pub struct DomainMap {
    pub domains: HashMap<SymbolId, Vec<HashSet<Value>>>,
    pub universe: HashSet<Value>,
}

impl DomainMap {
    pub fn from_program(program: &ast::Program, const_map: &HashMap<SymbolId, Value>) -> Self {
        let mut domains = HashMap::<SymbolId, Vec<HashSet<Value>>>::new();
        let mut universe = HashSet::new();
        for stmt in &program.statements {
            match stmt {
                Statement::Rule(r) => {
                    for h in &r.head {
                        collect_atom_domains(h, const_map, &mut domains, &mut universe);
                    }
                    for lit in &r.body {
                        collect_literal_domains(lit, const_map, &mut domains, &mut universe);
                    }
                }
                Statement::Constraint(c) => {
                    for lit in &c.body {
                        collect_literal_domains(lit, const_map, &mut domains, &mut universe);
                    }
                }
                Statement::Choice(ch) => {
                    for elem in &ch.elements {
                        collect_atom_domains(&elem.atom, const_map, &mut domains, &mut universe);
                    }
                    for lit in &ch.body {
                        collect_literal_domains(lit, const_map, &mut domains, &mut universe);
                    }
                }
                _ => {}
            }
        }
        Self { domains, universe }
    }

    pub fn values_for(&self, pred: SymbolId, pos: usize) -> Option<&HashSet<Value>> {
        self.domains.get(&pred).and_then(|v| v.get(pos))
    }
}

fn collect_atom_domains(
    atom: &ast::Atom,
    const_map: &HashMap<SymbolId, Value>,
    domains: &mut HashMap<SymbolId, Vec<HashSet<Value>>>,
    universe: &mut HashSet<Value>,
) {
    let entry = domains.entry(atom.predicate).or_insert_with(|| vec![HashSet::new(); atom.args.len()]);
    if entry.len() < atom.args.len() {
        entry.resize(atom.args.len(), HashSet::new());
    }
    for (i, arg) in atom.args.iter().enumerate() {
        collect_ground_values(arg, const_map, &mut entry[i], universe);
    }
}

fn collect_literal_domains(
    lit: &ast::Literal,
    const_map: &HashMap<SymbolId, Value>,
    domains: &mut HashMap<SymbolId, Vec<HashSet<Value>>>,
    universe: &mut HashSet<Value>,
) {
    let ba = match lit {
        ast::Literal::Pos(ba) | ast::Literal::Neg(ba) => ba,
    };
    if let ast::BodyAtom::Atom(a) = ba {
        collect_atom_domains(a, const_map, domains, universe);
    }
}

/// Extract ground constants from a term into the value sets.
fn collect_ground_values(
    term: &Term,
    const_map: &HashMap<SymbolId, Value>,
    set: &mut HashSet<Value>,
    universe: &mut HashSet<Value>,
) {
    match term {
        Term::Integer(n) => { let v = Value::Int(*n); set.insert(v.clone()); universe.insert(v); }
        Term::Symbolic(s) => {
            if let Some(v) = const_map.get(s) {
                set.insert(v.clone());
                universe.insert(v.clone());
            } else {
                let v = Value::Sym(*s);
                set.insert(v.clone());
                universe.insert(v);
            }
        }
        Term::Range(lo, hi) => {
            // Expand constant ranges
            if let (Term::Integer(a), Term::Integer(b)) = (lo.as_ref(), hi.as_ref()) {
                for i in *a..=*b {
                    let v = Value::Int(i);
                    set.insert(v.clone());
                    universe.insert(v);
                }
            }
        }
        _ => {} // Variables, functions, etc. — not ground constants
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::parser;

    #[test]
    fn domain_from_facts() {
        let mut interner = Interner::new();
        let prog = parser::parse("p(1). p(2). q(a).", &mut interner).unwrap();
        let dm = DomainMap::from_program(&prog, &HashMap::new());
        let p_id = interner.intern("p");
        let vals = dm.values_for(p_id, 0).unwrap();
        assert!(vals.contains(&Value::Int(1)));
        assert!(vals.contains(&Value::Int(2)));
        assert_eq!(vals.len(), 2);
    }
}
