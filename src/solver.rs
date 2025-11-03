use std::iter;

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

    pub satisfied_clauses: Vec<Vec<usize>>, // (decision_level, satisfied_clause_indices)
}

pub fn DPLL(problem: &Problem, solver_state: &mut SolverState, level: u32) -> SATResult {
    solver_state.trail_lim.push(solver_state.prop_head);
    unit_propagation(&problem.clauses, solver_state, level);

    // if Φ is empty then
    //     return SATResult::SATISFIABLE;

    // if Φ contains an empty clause then
    //     return SATResult::UNSATISFIABLE;

    // l ← choose-literal(Φ);
    // return DPLL(Φ ∧ {l}) or DPLL(Φ ∧ {¬l});

    return SATResult::SATISFIABLE;
}

fn unit_propagation(clauses: &Vec<Clause>, mut solver_state: &mut SolverState, level: u32) {
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

    for i in 0..clauses.len() {
        if sat_clauses.contains(&i) {
            // no need to check since it is statisfied
            continue;
        } else {
            if clauses[i].lits.len() == 1 {
                let literal = clauses[i].lits[0];
                let truth_value = solver_state.values.get_mut(literal.var.0 as usize).unwrap();
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

        if solver_state.prop_head == solver_state.trail.len() {
            // we found no units to propagate
            solver_state.satisfied_clauses.push(sat_clauses);
            break;
        }

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
                    if literal.var.0 == unit_idx as u32 {
                        if literal.positive && taget_lit_value == Truth::True
                            || !literal.positive && taget_lit_value == Truth::False
                        {
                            // clause will be statisfied
                            sat_clauses.push(clause_idx);
                        }
                    }
                }
            }
        }
    }
}

fn pure_literal_elimination() {}

fn choose_first_literal(clauses: &Vec<Vec<i32>>) -> i32 {}

fn build_model(solver_state: &SolverState) -> Vec<bool> {}
