use crate::problem::*;

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

    pub satisfied_clauses: Vec<(usize, Vec<usize>)>, // (decision_level, satisfied_clause_indices)
}

pub fn DPLL(problem: &Problem, mut solver_state: &SolverState) -> SATResult {
    unit_propagation(&problem.clauses, solver_state);

    // if Φ is empty then
    //     return SATResult::SATISFIABLE;

    // if Φ contains an empty clause then
    //     return SATResult::UNSATISFIABLE;

    // l ← choose-literal(Φ);
    // return DPLL(Φ ∧ {l}) or DPLL(Φ ∧ {¬l});

    return SATResult::SATISFIABLE;
}

fn unit_propagation(clauses: &Vec<Clause>, mut solver_state: &SolverState) {}

fn pure_literal_elimination() {
    // find all pure literals
    // go over each clause if they contain pure literals then remove them
}

fn choose_first_literal(clauses: &Vec<Vec<i32>>) -> i32 {}

fn build_model(solver_state: &SolverState) -> Vec<bool> {}
