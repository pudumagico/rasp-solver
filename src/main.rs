use std::io::Read;
use std::process;
use std::time::Instant;

const VERSION: &str = "rasp-solver 0.1.0";
const HELP: &str = "\
Usage: asp-solver [OPTIONS] [FILE]

Read ASP program from FILE (or stdin) and compute answer sets.

Options:
  -n N       Number of models (0 = all, default 1)
  --stats    Print solver statistics to stderr
  -h, --help Show this help
  --version  Print version info";

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut num_models = 1usize;
    let mut file_path = None;
    let mut show_stats = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => { println!("{HELP}"); process::exit(0); }
            "--version" => { println!("{VERSION}"); process::exit(0); }
            "--stats" => { show_stats = true; }
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

    let t_start = Instant::now();
    let mut interner = asp_solver::interner::Interner::new();
    let program = match asp_solver::parser::parse(&input, &mut interner) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(0);
        }
    };

    let has_optimize = program.statements.iter()
        .any(|s| matches!(s, asp_solver::parser::ast::Statement::Optimize(_)));

    let t_ground_start = Instant::now();
    let ground = match asp_solver::grounder::ground(&program, &mut interner) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Grounding error: {e}");
            process::exit(0);
        }
    };
    let t_ground = t_ground_start.elapsed();

    let t_solve_start = Instant::now();
    let exit_code;

    if has_optimize {
        let opt_specs = asp_solver::grounder::ground_optimize(&program, &ground, &interner);
        exit_code = solve_optimize(&ground, &interner, &opt_specs);
    } else if num_models == 1 {
        let result = asp_solver::solver::solve(&ground);
        exit_code = print_and_exit_code(&result, &ground, &interner);
    } else {
        let models = asp_solver::solver::solve_many(&ground, num_models);
        if models.is_empty() {
            println!("UNSATISFIABLE");
            exit_code = 20;
        } else {
            for (i, model) in models.iter().enumerate() {
                let result = asp_solver::solver::SolveResult::Satisfiable(model.clone());
                if models.len() > 1 { println!("Answer: {}", i + 1); }
                asp_solver::output::print_result(&result, &ground, &interner);
            }
            exit_code = 10;
        }
    }
    let t_solve = t_solve_start.elapsed();

    if show_stats {
        eprintln!("Grounding : {:.3}s", t_ground.as_secs_f64());
        eprintln!("Solving   : {:.3}s", t_solve.as_secs_f64());
        eprintln!("Total     : {:.3}s", t_start.elapsed().as_secs_f64());
        eprintln!("Atoms     : {}", ground.atom_table.len());
        eprintln!("Rules     : {}", ground.rules.len());
    }

    process::exit(exit_code);
}

fn print_and_exit_code(
    result: &asp_solver::solver::SolveResult,
    ground: &asp_solver::ground::program::GroundProgram,
    interner: &asp_solver::interner::Interner,
) -> i32 {
    asp_solver::output::print_result(result, ground, interner);
    match result {
        asp_solver::solver::SolveResult::Satisfiable(_) => 10,
        asp_solver::solver::SolveResult::Unsatisfiable => 20,
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
) -> i32 {
    use asp_solver::solver::SolveResult;

    // Iterative optimization: find a model, block worse/equal costs, repeat
    let models = asp_solver::solver::solve_many(ground, 0);
    if models.is_empty() {
        println!("UNSATISFIABLE");
        return 20;
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
    30 // ASP-comp: OPTIMUM FOUND
}
