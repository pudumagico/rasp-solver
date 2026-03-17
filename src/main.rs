use std::io::Read;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let input = match args.get(1) {
        Some(path) => std::fs::read_to_string(path).unwrap_or_else(|e| {
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

    let program = match asp_solver::parser::parse(&input) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(1);
        }
    };

    let ground = asp_solver::grounder::ground(&program);
    let result = asp_solver::solver::solve(&ground);
    asp_solver::output::print_result(&result, &ground);
}
