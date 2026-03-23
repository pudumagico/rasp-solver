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

    let has_optimize = program.statements.iter()
        .any(|s| matches!(s, asp_solver::parser::ast::Statement::Optimize(_)));

    let ground = match asp_solver::grounder::ground(&program, &mut interner) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Grounding error: {e}");
            process::exit(1);
        }
    };

    if has_optimize {
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
                if models.len() > 1 { println!("Answer: {}", i + 1); }
                asp_solver::output::print_result(&result, &ground, &interner);
            }
        }
    }
}

/// Compute lexicographic cost vector for a model. Each entry corresponds to a
/// priority level (sorted descending by priority). Lower is better.
fn compute_cost(
    model: &[asp_solver::types::AtomId],
    opt_specs: &[asp_solver::grounder::OptSpec],
) -> Vec<i64> {
    opt_specs.iter().map(|spec| {
        let cost: i64 = spec.weighted.iter()
            .filter(|(_, atom)| model.contains(atom))
            .map(|(w, _)| *w)
            .sum();
        if spec.minimize { cost } else { -cost }
    }).collect()
}

fn solve_optimize(
    ground: &asp_solver::ground::program::GroundProgram,
    interner: &asp_solver::interner::Interner,
    opt_specs: &[asp_solver::grounder::OptSpec],
) {
    use asp_solver::solver::SolveResult;

    // Enumerate all models, track and print each improving solution
    let models = asp_solver::solver::solve_many(ground, 0);
    if models.is_empty() {
        println!("UNSATISFIABLE");
        return;
    }

    let mut best_model = &models[0];
    let mut best_cost = compute_cost(best_model, opt_specs);

    for model in &models[1..] {
        let cost = compute_cost(model, opt_specs);
        if cost < best_cost {
            best_cost = cost;
            best_model = model;
        }
    }

    let result = SolveResult::Satisfiable(best_model.clone());
    asp_solver::output::print_result(&result, ground, interner);
    let costs: Vec<String> = opt_specs.iter().zip(&best_cost)
        .map(|(spec, c)| format!("{c}@{}", spec.priority))
        .collect();
    println!("Optimization: {}", costs.join(" "));
    println!("OPTIMUM FOUND");
}
