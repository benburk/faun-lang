//! Whether every definition stops.
//!
//! A definition may go round only on something it took apart, so each time
//! round is over something strictly smaller and the taking apart has an
//! end. What that takes is two things: knowing, of every value a body
//! holds, what it is against the parameters it came from; and knowing, of
//! every way round the call graph, that something gets smaller.
//!
//! Those two are kept apart here because the second is where this grows.
//! What a call does to the sizes it carries is read into a matrix -- rows
//! the parameters it was handed, columns the arguments it hands on -- and
//! the verdict is read off the matrices. Today it is read off each of them
//! on its own: a way round descends when one column descends in every call
//! along it.
//!
//! Size-change termination is the same reading over the *closure of those
//! matrices under composition*. A pair of definitions shrinking different
//! arguments by turns -- `merge` taking one list apart in one arm and the
//! other in the other -- descends every way round without descending at any
//! single call, and no reading of one matrix at a time can see it. Composing
//! them is what this grows into, and the matrices are the seam: what the
//! walk below answers would not change, only what is asked of it.

use std::collections::HashMap;

use super::ir::{Atom, Body, Expr, ExprId, FnId, Program};

/// What a value is, against a parameter it came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    /// Taken out of it, and so strictly smaller than it.
    Smaller,
    /// It, or something else no bigger and no smaller.
    Same,
    /// Nothing that can be said. What a call answers is this, until
    /// something says what a call answers.
    Unknown,
}

/// What one call does to the sizes it carries: a row per parameter it was
/// handed, a column per argument it hands on.
#[derive(Debug)]
struct Matrix {
    columns: usize,
    cells: Vec<Step>,
}

impl Matrix {
    fn at(&self, row: usize, column: usize) -> Step {
        self.cells
            .get(row * self.columns + column)
            .copied()
            .unwrap_or(Step::Unknown)
    }
}

/// Refuse a definition nothing shows stops.
pub(super) fn stops(program: &Program) -> Result<(), String> {
    let calls = graph(program);
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let round: Vec<FnId> = (0..program.functions().len())
            .map(FnId::at)
            .filter(|held| reaches(&calls, id, *held) && reaches(&calls, *held, id))
            .collect();
        // Read each way round once, from the first definition in it.
        if !reaches(&calls, id, id) || round.first() != Some(&id) {
            continue;
        }
        descends(program, &round)?;
    }
    Ok(())
}

/// One column that descends at every call round, which is this reading of
/// the matrices. The column is the same one throughout on purpose: one
/// definition taking its first argument apart and the next taking its
/// second is two things getting smaller by turns, and reading the calls one
/// at a time cannot tell that from neither of them running out.
fn descends(program: &Program, round: &[FnId]) -> Result<(), String> {
    let held: Vec<Vec<Matrix>> = round
        .iter()
        .map(|id| matrices(program, *id, round))
        .collect();
    let widest = round
        .iter()
        .map(|id| program.params(*id).len())
        .min()
        .unwrap_or(0);

    for column in 0..widest {
        if held
            .iter()
            .flatten()
            .all(|matrix| matrix.at(column, column) == Step::Smaller)
        {
            return Ok(());
        }
    }

    let named: Vec<&str> = round
        .iter()
        .map(|id| program.name(program.function(*id).name))
        .collect();
    Err(format!(
        "nothing here shows `{}` stops: it goes round on what it was handed rather than on a part of it",
        named.join("`, `")
    ))
}

/// A matrix per call this definition makes to one it goes round with.
fn matrices(program: &Program, id: FnId, round: &[FnId]) -> Vec<Matrix> {
    let params = program.params(id).len();
    let mut held = Vec::new();
    let Some(body) = program.function(id).body else {
        return held;
    };
    // A parameter is itself and no part of itself: going round on the whole
    // of what you were handed is going round for ever.
    let mut sizes: Vec<Vec<Step>> = (0..params)
        .map(|at| {
            let mut row = vec![Step::Unknown; params];
            row[at] = Step::Same;
            row
        })
        .collect();
    read(program, body, round, (&mut sizes, &mut held, params));
    held
}

/// Each binding takes the next level, and what an arm takes apart is
/// smaller than what it took it out of.
fn read(
    program: &Program,
    body: Body,
    round: &[FnId],
    (sizes, held, params): (&mut Vec<Vec<Step>>, &mut Vec<Matrix>, usize),
) {
    for binding in program.bindings(body.bindings).to_vec() {
        term(program, binding, round, (sizes, held, params));
        sizes.push(vec![Step::Unknown; params]);
    }
    term(program, body.tail, round, (sizes, held, params));
}

fn term(
    program: &Program,
    id: ExprId,
    round: &[FnId],
    (sizes, held, params): (&mut Vec<Vec<Step>>, &mut Vec<Matrix>, usize),
) {
    match program.expr(id) {
        Expr::Call(called, args) if round.contains(&called) => {
            let args = program.atoms(args).to_vec();
            held.push(matrix(sizes, &args, params));
        }
        Expr::Match(scrutinee, arms) => {
            let of = taken(sizes, scrutinee);
            for arm in program.arms(arms).to_vec() {
                let level = sizes.len();
                sizes.resize(level + program.fields(arm.ctor).len(), of.clone());
                read(program, arm.body, round, (sizes, held, params));
                sizes.truncate(level);
            }
        }
        Expr::Atom(_) | Expr::Con(..) | Expr::Static(..) | Expr::Call(..) => {}
    }
}

/// What a constructor's fields are, against the parameters the value it was
/// taken out of came from: smaller than whatever that was, and smaller than
/// what that was already smaller than.
fn taken(sizes: &[Vec<Step>], scrutinee: Atom) -> Vec<Step> {
    let held = sizes.get(scrutinee.0.index());
    held.map_or_else(Vec::new, |held| {
        held.iter()
            .map(|step| match step {
                Step::Same | Step::Smaller => Step::Smaller,
                Step::Unknown => Step::Unknown,
            })
            .collect()
    })
}

/// What one call hands on, read off the sizes of what it hands.
fn matrix(sizes: &[Vec<Step>], args: &[Atom], params: usize) -> Matrix {
    let mut cells = vec![Step::Unknown; params * args.len()];
    for (column, arg) in args.iter().enumerate() {
        let Some(held) = sizes.get(arg.0.index()) else {
            continue;
        };
        for (row, step) in held.iter().enumerate() {
            cells[row * args.len() + column] = *step;
        }
    }
    Matrix {
        columns: args.len(),
        cells,
    }
}

/// Which definitions each one calls.
fn graph(program: &Program) -> HashMap<FnId, Vec<FnId>> {
    fn within(program: &Program, body: Body, held: &mut Vec<FnId>) {
        for expr in program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
            .copied()
        {
            match program.expr(expr) {
                Expr::Call(called, _) => held.push(called),
                Expr::Match(_, arms) => {
                    for arm in program.arms(arms) {
                        within(program, arm.body, held);
                    }
                }
                Expr::Atom(_) | Expr::Con(..) | Expr::Static(..) => {}
            }
        }
    }
    (0..program.functions().len())
        .map(|at| {
            let id = FnId::at(at);
            let mut held = Vec::new();
            if let Some(body) = program.function(id).body {
                within(program, body, &mut held);
            }
            (id, held)
        })
        .collect()
}

fn reaches(calls: &HashMap<FnId, Vec<FnId>>, from: FnId, to: FnId) -> bool {
    let mut seen = vec![from];
    let mut waiting = vec![from];
    while let Some(at) = waiting.pop() {
        for called in calls.get(&at).into_iter().flatten() {
            if *called == to {
                return true;
            }
            if !seen.contains(called) {
                seen.push(*called);
                waiting.push(*called);
            }
        }
    }
    false
}
