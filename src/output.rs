use crate::ground::program::{GroundAtom, GroundProgram};
use crate::interner::Interner;
use crate::solver::SolveResult;
use crate::types::Value;

/// Print result in ASP Competition format.
pub fn print_result(result: &SolveResult, program: &GroundProgram, interner: &Interner) {
    match result {
        SolveResult::Satisfiable(atoms) => {
            let shown: Vec<String> = atoms
                .iter()
                .filter(|id| program.show_all || program.show_atoms.contains(id))
                .filter(|id| {
                    // Skip internal auxiliary atoms (__ prefix) but keep __neg_ (classical negation)
                    let atom = program.atom_table.resolve(**id);
                    let name = interner.resolve(atom.predicate);
                    !name.starts_with("__") || name.starts_with("__neg_")
                })
                .map(|id| format_atom(program.atom_table.resolve(*id), interner))
                .collect();
            println!("{}", shown.join(" "));
            println!("SATISFIABLE");
        }
        SolveResult::Unsatisfiable => {
            println!("UNSATISFIABLE");
        }
    }
}

fn format_atom(atom: &GroundAtom, interner: &Interner) -> String {
    let raw_name = interner.resolve(atom.predicate);
    // Render __neg_p as -p for classical negation
    let name = raw_name.strip_prefix("__neg_")
        .map(|n| format!("-{n}"))
        .unwrap_or_else(|| raw_name.to_string());
    if atom.args.is_empty() {
        name
    } else {
        let args: Vec<String> = atom.args.iter().map(|v| format_value(v, interner)).collect();
        format!("{name}({})", args.join(","))
    }
}

fn format_value(v: &Value, interner: &Interner) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Sym(s) => interner.resolve(*s).to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format_atom_no_args() {
        let mut interner = Interner::new();
        let pred = interner.intern("a");
        let atom = GroundAtom { predicate: pred, args: vec![] };
        assert_eq!(format_atom(&atom, &interner), "a");
    }

    #[test]
    fn format_atom_with_args() {
        let mut interner = Interner::new();
        let pred = interner.intern("p");
        let sym = interner.intern("foo");
        let atom = GroundAtom { predicate: pred, args: vec![Value::Int(1), Value::Sym(sym)] };
        assert_eq!(format_atom(&atom, &interner), "p(1,foo)");
    }
}
