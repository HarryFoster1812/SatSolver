use std::{collections::HashMap, iter, ops::Not};

use crate::{problem::*, solver};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SATResult {
    SATISFIABLE,
    UNSATISFIABLE,
}

impl SATResult {
    pub fn to_string(self) -> &'static str {
        if self == SATResult::SATISFIABLE {
            "SATISFIABLE"
        } else {
            "UNSATISFIABLE"
        }
    }
}

#[derive(Debug)]
pub struct SolverResult {
    pub status: SATResult,
    pub model: Vec<bool>,
}

#[derive(Debug)]
pub struct SolverState {
    // Per-variable assignment
    pub values: Vec<Truth>,

    // Decision stack / undo log
    pub trail: Vec<Literal>,
    pub trail_lim: Vec<usize>,

    pub satisfied_clauses: Vec<Vec<usize>>, // satisfied_clause_indices
}

pub fn solve(problem: &Problem, solver_state: &mut SolverState) -> SolverResult {
    match DPLL(problem, solver_state, 0) {
        true => SolverResult {
            status: SATResult::SATISFIABLE,
            model: Vec::new(),
        },
        false => SolverResult {
            status: SATResult::UNSATISFIABLE,
            model: Vec::new(),
        },
    }
}

pub fn DPLL(problem: &Problem, solver_state: &mut SolverState, level: u32) -> bool {
    solver_state.trail_lim.push(solver_state.trail.len()); // the current head of all of the
    // decisions

    // make sure that there is a slot for the sat_clauses
    ensure_level_slot(solver_state, level as usize);

    if !unit_propagation(&problem.clauses, solver_state, level) {
        // there was a contradiction so we return false
        return false;
    }

    pure_literal_elimination(&problem.clauses, solver_state, level);

    // check if all clauses are satisfied
    if solver_state
        .satisfied_clauses
        .get(level as usize)
        .unwrap()
        .len()
        == problem.clauses.len()
    {
        return true;
    }

    let l = choose_literal(&problem.clauses, solver_state, level as usize).unwrap();

    // println!("Level:{}\n{:?}", level, solver_state);
    *solver_state.values.get_mut((l.var.0) as usize).unwrap() = Truth::True;
    solver_state.trail.push(l);

    // println!("CHOSE LITERAL: {}", l.var.0);
    // println!();
    return if DPLL(problem, solver_state, level + 1) {
        true
    } else {
        // println!("LITERAL ID {} CAUSED CONTRADICTION", l.var.0);
        // println!("UNDOING ON LEVEL: {}", level);
        undo_solve(solver_state, level + 1);

        *solver_state.values.get_mut((l.var.0) as usize).unwrap() = Truth::False;

        solver_state
            .trail
            .last_mut()
            .expect("Last literal not found")
            .positive
            .not();

        // println!("AFTER UNDO");
        // println!("{:?}", solver_state);

        DPLL(problem, solver_state, level + 1)
    };
}

fn unit_propagation(clauses: &Vec<Clause>, solver_state: &mut SolverState, level: u32) -> bool {
    // Build a 'satisfied' bitmap for convenience
    let mut is_sat = vec![false; clauses.len()];
    if level > 0 {
        if let Some(level_clauses) = solver_state.satisfied_clauses.get(level as usize) {
            for &ci in level_clauses {
                if ci < is_sat.len() {
                    is_sat[ci] = true;
                }
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;

        for (ci, clause) in clauses.iter().enumerate() {
            if is_sat[ci] {
                continue;
            }

            let mut has_true = false;
            let mut undef_count = 0usize;
            let mut last_undef = 0usize;

            for (li, lit) in clause.lits.iter().enumerate() {
                let v = solver_state.values[lit.var.0 as usize];
                match v {
                    Truth::Undef => {
                        undef_count += 1;
                        last_undef = li;
                    }
                    Truth::True if lit.positive => {
                        has_true = true;
                        break;
                    }
                    Truth::False if !lit.positive => {
                        has_true = true;
                        break;
                    }
                    _ => {}
                }
            }

            if has_true {
                is_sat[ci] = true;
                continue;
            }

            if undef_count == 0 {
                // conflict: all literals are false
                return false;
            }

            if undef_count == 1 {
                // Unit clause
                let lit = clause.lits[last_undef];
                let slot = &mut solver_state.values[lit.var.0 as usize];
                match *slot {
                    Truth::Undef => {
                        *slot = if lit.positive {
                            Truth::True
                        } else {
                            Truth::False
                        };
                        solver_state.trail.push(Literal {
                            var: lit.var,
                            positive: lit.positive,
                        });
                        changed = true;
                    }
                    Truth::True | Truth::False => {
                        let lit_is_true = (*slot == Truth::True && lit.positive)
                            || (*slot == Truth::False && !lit.positive);
                        if !lit_is_true {
                            return false;
                        }
                    }
                }
            }
        }
    }

    let sat_indices: Vec<usize> = is_sat
        .iter()
        .enumerate()
        .filter_map(|(i, &b)| if b { Some(i) } else { None })
        .collect();

    // println!("UNIT PROP FINISHED: {:?}", sat_indices);

    solver_state.satisfied_clauses[level as usize] = sat_indices;
    true
}

fn pure_literal_elimination(clauses: &[Clause], solver_state: &mut SolverState, level: u32) {
    let sat_clauses = solver_state
        .satisfied_clauses
        .get_mut((level) as usize)
        .unwrap();

    let mut pure_lits: HashMap<u32, (bool, bool)> = HashMap::new(); // (is_pure,first_seen_positive)
    for clause_idx in 0..clauses.len() {
        let clause = clauses.get(clause_idx).unwrap();
        if sat_clauses.contains(&clause_idx) {
            // clause already satisfied
            continue;
        }

        // for each literal in the clause
        for literal in clause.lits.iter() {
            if *solver_state.values.get((literal.var.0) as usize).unwrap() == Truth::Undef {
                if pure_lits.contains_key(&literal.var.0) {
                    let is_pure_so_far: bool = pure_lits.get(&literal.var.0).unwrap().0;
                    let has_same_sign: bool =
                        pure_lits.get(&literal.var.0).unwrap().1 == literal.positive;

                    if !is_pure_so_far || !has_same_sign {
                        pure_lits.get_mut(&literal.var.0).unwrap().0 = false;
                    }
                } else {
                    // add the key
                    pure_lits.insert(literal.var.0, (true, literal.positive));
                }
            }
        }
    }

    for (var_id, value) in pure_lits.into_iter() {
        if value.0 {
            // it is a pure literal
            solver_state.trail.push(Literal {
                var: VariableId(var_id),
                positive: value.1,
            });

            // update clauses to remove the ones that the literal statisfies

            for clause_idx in 0..clauses.len() {
                let clause = clauses.get(clause_idx).unwrap();
                if sat_clauses.contains(&clause_idx) {
                    // clause already satisfied
                    continue;
                }

                // for each literal in the clause
                for literal in clause.lits.iter() {
                    // if literal is the target literal
                    if literal.var.0 == var_id {
                        sat_clauses.push(clause_idx);
                        break;
                    }
                }
            }

            *solver_state.values.get_mut((var_id) as usize).unwrap() =
                if value.1 { Truth::True } else { Truth::False }
        }
    }
}

fn choose_literal(
    clauses: &Vec<Clause>,
    solver_state: &mut SolverState,
    level: usize,
) -> Option<Literal> {
    let sat = solver_state
        .satisfied_clauses
        .get(level)
        .map(|v| v.as_slice())
        .unwrap_or(&[]);

    for i in 0..clauses.len() {
        if sat.contains(&i) {
            continue;
        }

        for lit in &clauses[i].lits {
            if solver_state.values[lit.var.0 as usize] == Truth::Undef {
                return Some(Literal {
                    var: VariableId(lit.var.0),
                    positive: true,
                });
            }
        }
    }
    None
}

fn undo_solve(solver_state: &mut SolverState, level: u32) {
    let start_idx = *solver_state.trail_lim.get(level as usize).unwrap();
    for i in start_idx..solver_state.trail.len() {
        // set the value back to unknown
        let lit = solver_state.trail.get(i).unwrap();
        *solver_state.values.get_mut((lit.var.0) as usize).unwrap() = Truth::Undef;
    }

    // need to remove the trail and reset the prop_head
    solver_state
        .trail
        .drain(start_idx..solver_state.trail.len());

    solver_state
        .trail_lim
        .drain(level as usize..solver_state.satisfied_clauses.len());

    solver_state
        .satisfied_clauses
        .drain(level as usize..solver_state.satisfied_clauses.len());
}

fn ensure_level_slot(solver_state: &mut SolverState, level: usize) {
    if solver_state.satisfied_clauses.len() <= level {
        solver_state.satisfied_clauses.resize(level + 1, Vec::new());
    }
}
