pub mod aggregate;
pub mod domain;
pub mod instantiate;
pub mod scc;
pub mod seminaive;

use std::collections::HashMap;

use crate::ground::program::GroundProgram;
use crate::interner::Interner;
use crate::parser::ast::{Program, Statement};
use crate::types::{AtomId, SymbolId, Value};

use instantiate::eval_term;

#[derive(Debug, thiserror::Error)]
pub enum GroundError {
    #[error("unstratifiable program: {0}")]
    Unstratifiable(String),
    #[error("grounding error: {0}")]
    Other(String),
}

pub fn ground(program: &Program, interner: &mut Interner) -> Result<GroundProgram, GroundError> {
    let const_map = collect_constants(program, interner);
    let strata = scc::stratify(program).map_err(GroundError::Unstratifiable)?;
    let mut gp = seminaive::evaluate(&strata, program, interner, &const_map);
    seminaive::dedup_rules(&mut gp.rules);
    Ok(gp)
}

/// Collect #const definitions into a map.
fn collect_constants(program: &Program, _interner: &mut Interner) -> HashMap<SymbolId, Value> {
    let mut map = HashMap::new();
    for stmt in &program.statements {
        if let Statement::Const(c) = stmt
            && let Some(val) = eval_term(&c.value, &HashMap::new(), &map) {
                map.insert(c.name, val);
            }
    }
    map
}

/// Ground optimization directives. Returns (weighted_atoms, is_minimize) pairs.
pub fn ground_optimize(
    program: &Program,
    ground: &GroundProgram,
    _interner: &Interner,
) -> Vec<(Vec<(i64, AtomId)>, bool)> {
    let const_map = HashMap::new();
    let mut results = Vec::new();
    for stmt in &program.statements {
        if let Statement::Optimize(opt) = stmt {
            let mut weighted = Vec::new();
            for elem in &opt.elements {
                let Some(Value::Int(w)) = eval_term(&elem.weight, &HashMap::new(), &const_map) else { continue; };
                // Find atoms matching the condition
                for lit in &elem.condition {
                    let ba = match lit {
                        crate::parser::ast::Literal::Pos(ba) => ba,
                        _ => continue,
                    };
                    if let crate::parser::ast::BodyAtom::Atom(a) = ba {
                        // Find all ground atoms matching this predicate
                        for i in 0..ground.atom_table.len() {
                            let atom = ground.atom_table.resolve(AtomId(i as u32));
                            if atom.predicate == a.predicate {
                                weighted.push((w, AtomId(i as u32)));
                            }
                        }
                    }
                }
            }
            results.push((weighted, opt.minimize));
        }
    }
    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    #[test]
    fn ground_simple() {
        let mut interner = Interner::new();
        let prog = parser::parse("a. b :- a.", &mut interner).unwrap();
        let gp = ground(&prog, &mut interner).unwrap();
        assert!(gp.atom_table.len() >= 2);
    }

    #[test]
    fn ground_with_const() {
        let mut interner = Interner::new();
        let prog = parser::parse("#const n = 3. p(n).", &mut interner).unwrap();
        let gp = ground(&prog, &mut interner).unwrap();
        assert_eq!(gp.atom_table.len(), 1);
        let atom = gp.atom_table.resolve(crate::types::AtomId(0));
        assert_eq!(atom.args[0], Value::Int(3));
    }
}
