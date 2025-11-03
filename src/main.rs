mod problem;
mod solver;

use crate::problem::*;
use crate::solver::*;

use std::io;

fn main() -> io::Result<()> {
    // parse the file into the problem struct
    let problem = problem::parse_stdin()?;

    println!(
        "File Parsed. NumVars: {}. NumClauses: {}.",
        problem.num_variables,
        problem.clauses.len()
    );

    let mut solver_state: SolverState = SolverState {
        values: Vec::with_capacity(problem.num_variables),
        decision_level: Vec::new(),
        trail: Vec::new(),
        trail_lim: Vec::new(),
        prop_head: 0,
        satisfied_clauses: Vec::new(),
    };

    solver_state.values.fill(Truth::Undef);

    let solver_result: SATResult = DPLL(&problem, &solver_state);

    print!("{}", solver_result.to_string());

    Ok(())
}
