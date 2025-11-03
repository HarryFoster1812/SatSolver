use std::{
    collections::HashMap,
    io::{self, BufRead},
};

/// A SAT problem: number of variables/clauses and the clauses themselves.

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct VariableId(pub u32); // internal var index (0-based)

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ClauseId(pub usize); // index into Problem.clauses

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Literal {
    pub var: VariableId,
    pub positive: bool, // true => x, false => ¬x
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Truth {
    True,
    False,
    Undef,
}

#[derive(Debug)]
pub struct Clause {
    pub lits: Box<[Literal]>, // fixed after construction
}

#[derive(Debug)]
pub struct Problem {
    pub num_variables: usize, // to size arrays
    pub clauses: Vec<Clause>, // the only owned copy of CNF
}

/// Parse DIMACS CNF from stdin into problem.
pub fn parse_stdin() -> io::Result<Problem> {
    let mut problem = Problem {
        num_variables: 0,
        clauses: vec![],
    };
    let stdin = io::stdin();
    for line_res in stdin.lock().lines() {
        let line = line_res?;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('c') {
            // comment or blank line
            continue;
        } else if trimmed.starts_with('p') {
            parse_problem_header(trimmed, &mut problem)?;
        } else {
            // clause line: sequence of ints ending with 0
            if let Some(clause) = parse_clause_line(trimmed)? {
                problem.clauses.push(clause);
            }
        }
    }
    Ok(problem)
}

/// Parse "p cnf <num_variables> <num_clauses>"
fn parse_problem_header(line: &str, problem: &mut Problem) -> io::Result<()> {
    // Expect tokens: ["p", "cnf", "<vars>", "<clauses>"]
    let mut it = line.split_whitespace();
    let p = it.next();
    let fmt = it.next();
    let vars = it.next();
    let clauses = it.next();

    let num_clauses: u32;

    match (p, fmt, vars, clauses) {
        (Some("p"), Some("cnf"), Some(v), Some(c)) => {
            problem.num_variables = v.parse::<usize>().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Invalid num_variables: {e}"),
                )
            })?;
            num_clauses = c.parse::<u32>().map_err(|e| {
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
    let mut lits: Vec<Literal> = Vec::new();
    let mut lits_seen: HashMap<u32, bool> = HashMap::new();

    for tok in line.split_whitespace() {
        let mut lit = tok.parse::<i32>().map_err(|e| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Invalid literal `{tok}`: {e}"),
            )
        })?;

        if lit == 0 {
            // End of this clause
            return Ok(if lits.is_empty() {
                None
            } else {
                Some(Clause {
                    lits: lits.into_boxed_slice(),
                })
            });
        } else {
            let lit_id: u32 = lit.wrapping_neg() as u32;
            let is_positive: bool = lit > 0;
            if lits_seen.contains_key(&lit_id) {
                // check is the lit seen is the opposite of what was previously seen
                if *lits_seen.get(&lit_id).unwrap() != is_positive {
                    // the clause is a tautology
                    return Ok(None);
                } else {
                    lits_seen.insert(lit_id, lit > 0);
                }
                lits.push(Literal {
                    var: VariableId(lit_id),
                    positive: lit > 0,
                });
            }
        }
    }
    // If there's no trailing 0 on the line invalid DIMACS
    Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "Clause line missing trailing 0",
    ))
}

// TODO: add tautology elim at parse time
