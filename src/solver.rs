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
    pub trail: Vec<(Literal, usize, ClauseId)>, // Literal decision, level assigned, reasoning
    pub trail_lim: Vec<usize>,

    pub satisfied_clauses: Vec<Vec<usize>>, // satisfied_clause_indices
}

pub fn solve(problem: &mut Problem, solver_state: &mut SolverState) -> SolverResult {
    match CDCL(problem, solver_state) {
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

pub fn CDCL(problem: &mut Problem, solver_state: &mut SolverState) -> bool {
    let mut level = 0;
    loop {
        let falsified = unit_propagation(&problem.clauses, solver_state, &level); // Unit propagation
        if falsified {
            if level == 0 {
                return false;
            };
            let c = analyze_conflict(&problem.clauses, solver_state); // Build the learned clause
            problem.clauses.push(c);
            undo_solve(solver_state, &mut level); // undo to a level derrived from C somehow
        } else {
            if all_assigned(solver_state) {
                return true;
            }
            add_new_level(solver_state, &mut level);
            let l =
                choose_literal(&problem.clauses, solver_state, level).expect("Expected a literal");
            set_literal(solver_state, &l, &level); // add it to the trail
        }
    }
}

fn unit_propagation(clauses: &Vec<Clause>, solver_state: &mut SolverState, level: &usize) -> bool {
    // Build a 'satisfied' bitmap for convenience
    let mut is_sat = vec![false; clauses.len()];
    if *level > 0 {
        if let Some(level_clauses) = solver_state.satisfied_clauses.get(*level) {
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
                        solver_state.trail.push((
                            Literal {
                                var: lit.var,
                                positive: lit.positive,
                            },
                            *level,
                            ClauseId(ci),
                        ));
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

    solver_state.satisfied_clauses[*level] = sat_indices;
    true
}

// fn pure_literal_elimination(clauses: &[Clause], solver_state: &mut SolverState, level: u32) {
//     let sat_clauses = solver_state
//         .satisfied_clauses
//         .get_mut((level) as usize)
//         .unwrap();
//
//     let mut pure_lits: HashMap<u32, (bool, bool)> = HashMap::new(); // (is_pure,first_seen_positive)
//     for clause_idx in 0..clauses.len() {
//         let clause = clauses.get(clause_idx).unwrap();
//         if sat_clauses.contains(&clause_idx) {
//             // clause already satisfied
//             continue;
//         }
//
//         // for each literal in the clause
//         for literal in clause.lits.iter() {
//             if *solver_state.values.get((literal.var.0) as usize).unwrap() == Truth::Undef {
//                 if pure_lits.contains_key(&literal.var.0) {
//                     let is_pure_so_far: bool = pure_lits.get(&literal.var.0).unwrap().0;
//                     let has_same_sign: bool =
//                         pure_lits.get(&literal.var.0).unwrap().1 == literal.positive;
//
//                     if !is_pure_so_far || !has_same_sign {
//                         pure_lits.get_mut(&literal.var.0).unwrap().0 = false;
//                     }
//                 } else {
//                     // add the key
//                     pure_lits.insert(literal.var.0, (true, literal.positive));
//                 }
//             }
//         }
//     }
//
//     for (var_id, value) in pure_lits.into_iter() {
//         if value.0 {
//             // it is a pure literal
//             solver_state.trail.push(Literal {
//                 var: VariableId(var_id),
//                 positive: value.1,
//             });
//
//             // update clauses to remove the ones that the literal statisfies
//
//             for clause_idx in 0..clauses.len() {
//                 let clause = clauses.get(clause_idx).unwrap();
//                 if sat_clauses.contains(&clause_idx) {
//                     // clause already satisfied
//                     continue;
//                 }
//
//                 // for each literal in the clause
//                 for literal in clause.lits.iter() {
//                     // if literal is the target literal
//                     if literal.var.0 == var_id {
//                         sat_clauses.push(clause_idx);
//                         break;
//                     }
//                 }
//             }
//
//             *solver_state.values.get_mut((var_id) as usize).unwrap() =
//                 if value.1 { Truth::True } else { Truth::False }
//         }
//     }
// }

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

fn undo_solve(solver_state: &mut SolverState, level: &mut usize) {
    let start_idx = *solver_state.trail_lim.get(*level).unwrap();
    for i in start_idx..solver_state.trail.len() {
        // set the value back to unknown
        let lit = solver_state.trail.get(i).unwrap();
        *solver_state.values.get_mut((lit.0.var.0) as usize).unwrap() = Truth::Undef;
    }

    // need to remove the trail and reset the prop_head
    solver_state
        .trail
        .drain(start_idx..solver_state.trail.len());

    solver_state
        .trail_lim
        .drain(*level..solver_state.satisfied_clauses.len());

    solver_state
        .satisfied_clauses
        .drain(*level..solver_state.satisfied_clauses.len());
}

fn ensure_level_slot(solver_state: &mut SolverState, level: usize) {
    if solver_state.satisfied_clauses.len() <= level {
        solver_state.satisfied_clauses.resize(level + 1, Vec::new());
    }
}

fn analyze_conflict(clauses: &[Clause], solver_state: &mut SolverState) -> Clause {
    unimplemented!();
}

fn all_assigned(solver_state: &SolverState) -> bool {
    unimplemented!();
}

fn add_new_level(solver_state: &mut SolverState, level: &mut usize) {
    unimplemented!();
}

fn set_literal(solver_state: &mut SolverState, l: &Literal, level: &usize) {
    unimplemented!()
}
