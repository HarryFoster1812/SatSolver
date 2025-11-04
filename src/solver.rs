use std::{collections::HashMap, iter};

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
    pub decision_level: Vec<u32>,

    // Decision stack / undo log
    pub trail: Vec<Literal>,
    pub trail_lim: Vec<usize>,
    pub prop_head: usize,

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
    solver_state.trail_lim.push(solver_state.prop_head);
    if !unit_propagation(&problem.clauses, solver_state, level) {
        // there was a contradiction so we return false
        return false;
    }

    pure_literal_elimination(&problem.clauses, solver_state, level);

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

    *solver_state.values.get_mut((l.var.0 - 1) as usize).unwrap() = Truth::True;
    solver_state.trail.push(l);

    return if DPLL(problem, solver_state, level + 1) {
        true
    } else {
        undo_solve(solver_state, level + 1);
        *solver_state.values.get_mut((l.var.0 - 1) as usize).unwrap() = Truth::False;

        solver_state.trail.push(Literal {
            var: l.var,
            positive: !l.positive,
        });
        DPLL(problem, solver_state, level + 1)
    };
}

fn unit_propagation(clauses: &Vec<Clause>, mut solver_state: &mut SolverState, level: u32) -> bool {
    let mut sat_clauses: Vec<usize>;

    if level > 0 {
        if let Some(level_clauses) = solver_state.satisfied_clauses.get((level - 1) as usize) {
            sat_clauses = level_clauses.clone(); // Make a copy of the clauses at that decision level
        } else {
            sat_clauses = vec![]; // No clauses at this level
        }
    } else {
        sat_clauses = vec![]; // No clauses if level is 0
    }
    find_units(&mut sat_clauses, clauses, solver_state);
    while solver_state.prop_head < solver_state.trail.len() {
        // now the literals have been found we need to propagate them
        // for each unpropagated literal
        for unit_idx in solver_state.prop_head..solver_state.trail.len() {
            // for each clause
            let taget_lit_value = *solver_state.values.get(unit_idx).unwrap();
            solver_state.prop_head += 1;
            for clause_idx in 0..clauses.len() {
                let clause = clauses.get(clause_idx).unwrap();
                if sat_clauses.contains(&clause_idx) {
                    // clause already satisfied
                    continue;
                }

                // for each literal in the clause
                for literal in clause.lits.iter() {
                    // if literal is the target literal
                    if literal.var.0 == (unit_idx + 1) as u32 {
                        // check if it will satisfy the clause
                        if literal.positive && taget_lit_value == Truth::True
                            || !literal.positive && taget_lit_value == Truth::False
                        {
                            // clause will be statisfied
                            sat_clauses.push(clause_idx);
                        } else {
                            // there is a contradiction
                            return false;
                        }
                    }
                }
            }
        }

        find_units(&mut sat_clauses, clauses, solver_state);
    }
    solver_state.satisfied_clauses.push(sat_clauses);
    return true;
}

fn find_units(
    sat_clauses: &mut Vec<usize>,
    clauses: &Vec<Clause>,
    mut solver_state: &mut SolverState,
) {
    for i in 0..clauses.len() {
        if sat_clauses.contains(&i) {
            // no need to check since it is statisfied
            continue;
        }
        if clauses[i].lits.len() == 1 {
            let literal = clauses[i].lits[0];

            let truth_value = solver_state
                .values
                .get_mut((literal.var.0 - 1) as usize)
                .unwrap();
            *truth_value = if literal.positive {
                solver_state.trail.push(Literal {
                    var: literal.var,
                    positive: true,
                });
                Truth::True
            } else {
                solver_state.trail.push(Literal {
                    var: literal.var,
                    positive: false,
                });
                Truth::False
            };
            sat_clauses.push(i);
        }
    }
}

fn pure_literal_elimination(clauses: &Vec<Clause>, solver_state: &mut SolverState, level: u32) {
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
            if *solver_state
                .values
                .get((literal.var.0 - 1) as usize)
                .unwrap()
                == Truth::Undef
            {
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

            *solver_state.values.get_mut((var_id - 1) as usize).unwrap() =
                if value.1 { Truth::True } else { Truth::False }
        }
    }
}

fn choose_literal(
    clauses: &Vec<Clause>,
    solver_state: &mut SolverState,
    level: usize,
) -> Option<Literal> {
    // go though the solverstate and find the first unknown literal
    // find the first literal that is in a unstatisfied clause and propagate it
    for i in 0..clauses.len() {
        if solver_state
            .satisfied_clauses
            .get(level)
            .unwrap()
            .contains(&i)
        {
            continue;
        }

        for lit in clauses.get(i).unwrap().lits.iter() {
            if *solver_state.values.get((lit.var.0 - 1) as usize).unwrap() == Truth::Undef {
                return Some(Literal {
                    var: VariableId(lit.var.0),
                    positive: true,
                });
            }
        }
    }

    // this should not ever reach here ...
    // this means we have assigned all of the varibales but the problem is not solved...
    return None;
}

fn undo_solve(solver_state: &mut SolverState, level: u32) {
    let start_idx = *solver_state.trail_lim.get(1).unwrap();
    for i in start_idx..solver_state.trail.len() {
        // set the value back to unknown
        let lit = solver_state.trail.get(i).unwrap();
        *solver_state
            .values
            .get_mut((lit.var.0 - 1) as usize)
            .unwrap() = Truth::Undef;
    }

    // need to remove the trail and reset the prop_head
    solver_state
        .trail
        .drain(start_idx..solver_state.trail.len());

    solver_state.prop_head = solver_state.trail.len();

    solver_state
        .trail_lim
        .remove(solver_state.trail_lim.len() - 1); // remove the trail lim
}
