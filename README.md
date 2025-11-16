# Rust SAT Solver

A simple **SAT (Boolean Satisfiability Problem) solver** implemented in Rust using the **DPLL algorithm** with unit propagation and pure literal elimination.

This project was created as a university challenge for fun and learning purposes.

---

## Features

* Parses **DIMACS CNF** format from standard input.
* Implements **DPLL algorithm** (backtracking search for SAT problems).
* Supports:

  * **Unit Propagation**
  * **Pure Literal Elimination**
* Outputs whether the problem is **SATISFIABLE** or **UNSATISFIABLE**.
* Maintains solver state with:

  * Variable assignments (`True`, `False`, `Undef`)
  * Decision trail and backtracking
  * Clause satisfaction tracking

---

## Usage

1. **Build the project**:

```bash
cargo build --release
```

2. **Run the solver with a DIMACS CNF file**:

```bash
cat example.cnf | cargo run --release
```

3. **Example output**:

```
SATISFIABLE
```

or

```
UNSATISFIABLE
```

---

## File Structure

```
src/
├── main.rs       # Entry point, reads DIMACS input and runs solver
├── problem.rs    # DIMACS CNF parsing, Problem/Clause/Literal structs
└── solver.rs     # DPLL solver, unit propagation, pure literal elimination
```

---

## Design Overview

### Problem Representation

* **VariableId** – 0-based index for each variable.
* **ClauseId** – Index of a clause in the problem.
* **Literal** – Variable + polarity (positive or negative).
* **Truth** – Current assignment of a variable: `True`, `False`, `Undef`.
* **Clause** – Fixed-size array of literals.
* **Problem** – Contains number of variables and all clauses.

### Solver State

* `values` – Current truth assignments for all variables.
* `trail` – Decision stack of literals for backtracking.
* `trail_lim` – Level markers for decision points.
* `satisfied_clauses` – Clauses satisfied at each decision level.

### Algorithm

1. **Unit Propagation** – Assign variables that are forced by unit clauses.
2. **Pure Literal Elimination** – Assign variables that appear with only one polarity.
3. **Decision Making** – Choose an unassigned literal to branch on.
4. **Backtracking** – Undo assignments if a contradiction is reached.
5. Repeat until all clauses are satisfied or a conflict is found.

---

## Notes

* Currently, the solver **does not return a satisfying assignment**; it only reports SAT/UNSAT.
* Tautology clauses are eliminated at parse time.
* Designed for **educational purposes** and small-to-medium CNF problems.

---

## Example DIMACS CNF

```
c Simple example
p cnf 3 3
1 -3 0
2 3 -1 0
-2 -3 0
```
