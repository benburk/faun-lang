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

pub(super) fn recursive(program: &Program) -> Vec<bool> {
    let calls = graph(program);
    let mut found = vec![false; calls.len()];
    for round in rounds(&calls) {
        if round.len() > 1 || calls[round[0].index()].contains(&round[0]) {
            for id in round {
                found[id.index()] = true;
            }
        }
    }
    found
}

/// Refuse a definition nothing shows stops.
pub(super) fn stops(program: &Program) -> Result<(), String> {
    let calls = graph(program);
    for round in rounds(&calls) {
        // One definition on its own goes round only if it calls itself.
        if round.len() == 1 && !calls[round[0].index()].contains(&round[0]) {
            continue;
        }
        descends(program, &round)?;
    }
    Ok(())
}

/// The rounds a program's calls make: every definition in one reaches every
/// other in it, and comes back.
///
/// Which is what a strongly connected component is, so it is found the way
/// one is: a single walk that gives every definition a number as it is
/// first reached, and closes a round when it finds one that reaches no
/// further back than itself. Asking instead whether each definition reaches
/// each other was a search per pair, and the pairs are the square of the
/// program.
fn rounds(calls: &[Vec<FnId>]) -> Vec<Vec<FnId>> {
    let mut state = Rounds {
        calls,
        reached: vec![usize::MAX; calls.len()],
        lowest: vec![usize::MAX; calls.len()],
        within: vec![false; calls.len()],
        stack: Vec::new(),
        next: 0,
        held: Vec::new(),
    };
    for at in 0..calls.len() {
        if state.reached[at] == usize::MAX {
            state.walk(FnId::at(at));
        }
    }
    state.held
}

/// The walk that finds them, with its own stack rather than the machine's:
/// a program may call deeper than there is room to recurse.
struct Rounds<'a> {
    calls: &'a [Vec<FnId>],
    /// When each definition was first reached, and the earliest anything it
    /// reaches was.
    reached: Vec<usize>,
    lowest: Vec<usize>,
    /// Which are on the stack, since only those can close a round.
    within: Vec<bool>,
    stack: Vec<FnId>,
    next: usize,
    held: Vec<Vec<FnId>>,
}

impl Rounds<'_> {
    fn walk(&mut self, from: FnId) {
        // Where the walk is, and which call out of it comes next.
        let mut going = vec![(from, 0)];
        self.enter(from);

        while let Some(&mut (at, ref mut step)) = going.last_mut() {
            let called = self.calls[at.index()].get(*step).copied();
            *step += 1;
            let Some(called) = called else {
                going.pop();
                self.close(at);
                if let Some(&mut (before, _)) = going.last_mut() {
                    self.lowest[before.index()] =
                        self.lowest[before.index()].min(self.lowest[at.index()]);
                }
                continue;
            };
            if self.reached[called.index()] == usize::MAX {
                self.enter(called);
                going.push((called, 0));
            } else if self.within[called.index()] {
                self.lowest[at.index()] = self.lowest[at.index()].min(self.reached[called.index()]);
            }
        }
    }

    fn enter(&mut self, at: FnId) {
        self.reached[at.index()] = self.next;
        self.lowest[at.index()] = self.next;
        self.next += 1;
        self.within[at.index()] = true;
        self.stack.push(at);
    }

    /// A definition reaching no further back than itself is where a round
    /// ends, and everything above it on the stack is in that round.
    fn close(&mut self, at: FnId) {
        if self.lowest[at.index()] != self.reached[at.index()] {
            return;
        }
        let mut round = Vec::new();
        while let Some(held) = self.stack.pop() {
            self.within[held.index()] = false;
            round.push(held);
            if held == at {
                break;
            }
        }
        // In the order they were written, which is the order a round reads
        // in and the order its matrices are built in.
        round.sort_unstable_by_key(|held| held.index());
        self.held.push(round);
    }
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
fn graph(program: &Program) -> Vec<Vec<FnId>> {
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
            held
        })
        .collect()
}
