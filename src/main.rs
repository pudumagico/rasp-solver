use std::io::Read;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut num_models = 1usize;
    let mut file_path = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-n" => {
                i += 1;
                num_models = args.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
                    eprintln!("Error: -n requires a number (0 = all)");
                    process::exit(1);
                });
            }
            s if s.starts_with('-') => {
                eprintln!("Unknown option: {s}");
                process::exit(1);
            }
            _ => { file_path = Some(args[i].clone()); }
        }
        i += 1;
    }

    let input = match file_path {
        Some(path) => std::fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("Error reading {path}: {e}");
            process::exit(1);
        }),
        None => {
            let mut buf = String::new();
            std::io::stdin().read_to_string(&mut buf).unwrap_or_else(|e| {
                eprintln!("Error reading stdin: {e}");
                process::exit(1);
            });
            buf
        }
    };

    let mut interner = asp_solver::interner::Interner::new();
    let program = match asp_solver::parser::parse(&input, &mut interner) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(1);
        }
    };

    // Check for optimization directives
    let has_optimize = program.statements.iter().any(|s| matches!(s, asp_solver::parser::ast::Statement::Optimize(_)));

    let ground = match asp_solver::grounder::ground(&program, &mut interner) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Grounding error: {e}");
            process::exit(1);
        }
    };

    if has_optimize {
        // Optimization mode: find optimal answer set
        let opt_specs = asp_solver::grounder::ground_optimize(&program, &ground, &interner);
        solve_optimize(&ground, &interner, &opt_specs);
    } else if num_models == 1 {
        let result = asp_solver::solver::solve(&ground);
        asp_solver::output::print_result(&result, &ground, &interner);
    } else {
        let models = asp_solver::solver::solve_many(&ground, num_models);
        if models.is_empty() {
            println!("UNSATISFIABLE");
        } else {
            for (i, model) in models.iter().enumerate() {
                let result = asp_solver::solver::SolveResult::Satisfiable(model.clone());
                if models.len() > 1 {
                    println!("Answer: {}", i + 1);
                }
                asp_solver::output::print_result(&result, &ground, &interner);
            }
        }
    }
}

fn solve_optimize(
    ground: &asp_solver::ground::program::GroundProgram,
    interner: &asp_solver::interner::Interner,
    opt_specs: &[(Vec<(i64, asp_solver::types::AtomId)>, bool)],
) {
    use asp_solver::solver::{SolveResult, solve};
    

    // Iterative optimization: find a model, then constrain cost to be strictly better
    let best_result = solve(ground);
    let SolveResult::Satisfiable(ref best_model) = best_result else {
        println!("UNSATISFIABLE");
        return;
    };

    // For now, just print the first answer set with its cost
    // Full iterative optimization would require adding clauses to the ground program
    // and re-solving, which needs a mutable solver interface.
    let mut total_cost = 0i64;
    for (weights, minimize) in opt_specs {
        let cost: i64 = weights.iter()
            .filter(|(_, atom)| best_model.contains(atom))
            .map(|(w, _)| *w)
            .sum();
        total_cost += if *minimize { cost } else { -cost };
    }
    asp_solver::output::print_result(&best_result, ground, interner);
    println!("Optimization: {total_cost}");
}
