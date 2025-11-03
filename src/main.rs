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

    Ok(())
}
