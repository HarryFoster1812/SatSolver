mod problem;
mod solver;

use crate::problem::*;
use crate::solver::*;

use std::io;

fn main() -> io::Result<()> {
    // parse the file into the problem struct
    let PROBLEM: Problem = problem::parse_stdin()?;

    println!(
        "File Parsed. NumVars: {}. NumClauses: {}.",
        PROBLEM.num_variables,
        PROBLEM.clauses.len()
    );

    for i in 0..PROBLEM.clauses.len() {
        let clause = &PROBLEM.clauses[i];
        for j in 0..clause.lits.len() {
            let lit = clause.lits.get(j).unwrap();
            if lit.positive {
                print!("{} ", lit.var.0);
            } else {
                print!("~{} ", lit.var.0);
            }
        }
        println!();
    }

    let mut solver_state: SolverState = SolverState {
        values: vec![Truth::Undef; PROBLEM.num_variables],
        decision_level: Vec::new(),
        trail: Vec::new(),
        trail_lim: Vec::new(),
        prop_head: 0,
        satisfied_clauses: Vec::new(),
    };

    let solver_result: SolverResult = solve(&PROBLEM, &mut solver_state);

    println!("{}", solver_result.status.to_string());

    Ok(())
}
