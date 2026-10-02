//! Which definitions call which: the call graph, the rounds it goes in, and
//! an order reading each definition after what it calls.
//!
//! A round is every definition that reaches every other through calls, so
//! one that calls itself, or several calling each other. Inlining copies a
//! definition into its callers only where that leaves no round without a
//! breaker, a definition kept whole; folding reads each definition after
//! what it calls, so a caller meets its callees' answers.

use super::model::{Expr, FnId};
use super::program::Program;

/// The definitions expanding a call of must not, so that expanding every
/// other one ends: in each round of calls, one that calls itself, and
/// enough of the rest that no way round is left among the others. Each of
/// the others can then be copied into its caller, which is how two
/// definitions calling each other become one that calls itself, and a call
/// of itself in tail position becomes a loop below.
pub(super) fn breakers(program: &Program) -> Vec<bool> {
    let calls = graph(program);
    let mut breaker = vec![false; calls.len()];
    for round in rounds(&calls) {
        for &id in &round {
            if calls[id.index()].contains(&id) {
                breaker[id.index()] = true;
            }
        }
        if round.len() == 1 {
            continue;
        }
        // Among the rest, break each way round still left, one definition
        // at a time, until none is.
        loop {
            let left: Vec<Vec<FnId>> = calls
                .iter()
                .enumerate()
                .map(|(at, callees)| {
                    if breaker[at] || !round.contains(&FnId::at(at)) {
                        return Vec::new();
                    }
                    callees
                        .iter()
                        .copied()
                        .filter(|callee| round.contains(callee) && !breaker[callee.index()])
                        .collect()
                })
                .collect();
            let cycles: Vec<_> = rounds(&left)
                .into_iter()
                .filter(|within| within.len() > 1)
                .collect();
            if cycles.is_empty() {
                break;
            }
            for within in cycles {
                let first = within.iter().min().expect("a round has a member");
                breaker[first.index()] = true;
            }
        }
    }
    breaker
}

/// Every definition, each after everything it calls, but for those calling
/// each other, which come together in no particular order.
pub(super) fn callees_first(program: &Program) -> Vec<FnId> {
    rounds(&graph(program)).into_iter().flatten().collect()
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
        // In the order they were written.
        round.sort_unstable_by_key(|held| held.index());
        self.held.push(round);
    }
}

/// Which definitions each one calls.
pub(super) fn graph(program: &Program) -> Vec<Vec<FnId>> {
    (0..program.functions().len())
        .map(|at| {
            let Some(body) = program.function(FnId::at(at)).body() else {
                return Vec::new();
            };
            super::walk::within(program, body)
                .filter_map(|expr| match program.expr(expr) {
                    Expr::Call(called, _) => Some(called),
                    _ => None,
                })
                .collect()
        })
        .collect()
}
