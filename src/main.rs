use std::io::{self, BufRead};

/// A clause is a list of ints (positive/negative for variable / negation).
type Clause = Vec<i32>;

/// A SAT problem: number of variables/clauses and the clauses themselves.
struct Problem {
    num_variables: u32,
    num_clauses: u32,
    clauses: Vec<Clause>,
}

enum SATResult {
    SATISFIABLE,
    UNSATISFIABLE,
}

impl SATResult {
    fn as_str(&self) -> &'static str {
        match self {
            SATResult::SATISFIABLE => "SATISFIABLE",
            SATResult::UNSATISFIABLE => "UNSATISFIABLE",
        }
    }
}

fn main() -> io::Result<()> {
    let mut problem = Problem {
        num_variables: 0,
        num_clauses: 0,
        clauses: vec![],
    };

    // parse the file into the problem struct
    parse_stdin(&mut problem)?;

    println!(
        "File Parsed. NumVars: {}. NumClauses: {}. Parsed {} clauses.",
        problem.num_variables,
        problem.num_clauses,
        problem.clauses.len()
    );

    Ok(())
}

/// Parse DIMACS CNF from stdin into `problem`.
fn parse_stdin(problem: &mut Problem) -> io::Result<()> {
    let stdin = io::stdin();
    for line_res in stdin.lock().lines() {
        let line = line_res?;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('c') {
            // comment or blank line
            continue;
        } else if trimmed.starts_with('p') {
            parse_problem_header(trimmed, problem)?;
        } else {
            // clause line: sequence of ints ending with 0
            if let Some(clause) = parse_clause_line(trimmed)? {
                problem.clauses.push(clause);
            }
        }
    }
    Ok(())
}

/// Parse "p cnf <num_variables> <num_clauses>"
fn parse_problem_header(line: &str, problem: &mut Problem) -> io::Result<()> {
    // Expect tokens: ["p", "cnf", "<vars>", "<clauses>"]
    let mut it = line.split_whitespace();
    let p = it.next();
    let fmt = it.next();
    let vars = it.next();
    let clauses = it.next();

    match (p, fmt, vars, clauses) {
        (Some("p"), Some("cnf"), Some(v), Some(c)) => {
            problem.num_variables = v.parse::<u32>().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Invalid num_variables: {e}"),
                )
            })?;
            problem.num_clauses = c.parse::<u32>().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Invalid num_clauses: {e}"),
                )
            })?;
            Ok(())
        }
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Invalid problem line: {line}"),
        )),
    }
}

/// Parse a single clause line: ints ending with 0.
/// Returns Ok(None) if the line had nothing but "0".
fn parse_clause_line(line: &str) -> io::Result<Option<Clause>> {
    let mut clause: Clause = Vec::new();
    for tok in line.split_whitespace() {
        let lit = tok.parse::<i32>().map_err(|e| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Invalid literal `{tok}`: {e}"),
            )
        })?;
        if lit == 0 {
            // End of this clause
            return Ok(if clause.is_empty() {
                None
            } else {
                Some(clause)
            });
        } else {
            clause.push(lit);
        }
    }
    // If there's no trailing 0 on the line invalid DIMACS
    Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "Clause line missing trailing 0",
    ))
}
