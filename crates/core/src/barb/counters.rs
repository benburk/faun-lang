//! A parameter a definition hands itself one more of on every call it makes
//! to itself, while handing another parameter the rest of itself -- a count
//! kept beside a walk down a list or a number. Their sum never changes as it
//! goes round, so the count is never more than the most any caller from
//! outside hands the two together: a loop's index is below the length of
//! what it walks.

use super::{Atom, Body, Expr, ExprId, FnId, Operation, Program, TypeShape, type_shape};

/// A count and the parameter whose rest is handed on beside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Counter {
    pub counter: usize,
    pub measure: usize,
}

/// Each definition's counters, by definition.
pub(super) fn counters(program: &Program, operations: &[Option<Operation>]) -> Vec<Vec<Counter>> {
    (0..program.functions().len())
        .map(|at| of(program, operations, FnId::at(at)))
        .collect()
}

fn of(program: &Program, operations: &[Option<Operation>], id: FnId) -> Vec<Counter> {
    let Some(body) = program.function(id).body() else {
        return Vec::new();
    };
    let count = program.params(id).len();
    let mut found = Walk {
        program,
        operations,
        id,
        wrote: vec![None; count],
        rest_of: vec![None; count],
        calls: Vec::new(),
    };
    found.body(body);
    if found.calls.is_empty() {
        return Vec::new();
    }
    let mut counters = Vec::new();
    for counter in 0..count {
        for measure in (0..count).filter(|&measure| measure != counter) {
            let held = found
                .calls
                .iter()
                .all(|call| call[counter].0 && call[measure].1 == Some(measure));
            if held {
                counters.push(Counter { counter, measure });
            }
        }
    }
    counters
}

struct Walk<'a> {
    program: &'a Program,
    operations: &'a [Option<Operation>],
    id: FnId,
    /// What wrote each local, by level, where a binding did.
    wrote: Vec<Option<ExprId>>,
    /// Which parameter each local is the rest of, where a match on that
    /// parameter bound it as its constructor's recursive field.
    rest_of: Vec<Option<usize>>,
    /// Of each argument of every call the definition makes to itself,
    /// whether it is its own parameter stepped by one, and which parameter
    /// it is the rest of.
    calls: Vec<Vec<(bool, Option<usize>)>>,
}

impl Walk<'_> {
    fn body(&mut self, body: Body) {
        let level = self.wrote.len();
        for &binding in self.program.bindings(body.bindings) {
            self.expr(binding);
            self.wrote.push(Some(binding));
            self.rest_of.push(None);
        }
        self.expr(body.tail);
        self.wrote.truncate(level);
        self.rest_of.truncate(level);
    }

    fn expr(&mut self, id: ExprId) {
        match self.program.expr(id) {
            Expr::Call(called, args) if called == self.id => {
                let call = self
                    .program
                    .atoms(args)
                    .iter()
                    .enumerate()
                    .map(|(at, &arg)| {
                        let rest = self.rest_of.get(arg.0.index()).copied().flatten();
                        (self.stepped(arg, at), rest)
                    })
                    .collect();
                self.calls.push(call);
            }
            Expr::Match(Atom(on), arms) => {
                let parameter = (on.index() < self.program.params(self.id).len()
                    && self.wrote[on.index()].is_none())
                .then_some(on.index());
                for arm in self.program.arms(arms) {
                    let level = self.wrote.len();
                    let recursive = self.recursive(arm.ctor);
                    for at in 0..self.program.fields(arm.ctor).len() {
                        self.wrote.push(None);
                        self.rest_of
                            .push(parameter.filter(|_| recursive == Some(at)));
                    }
                    self.body(arm.body);
                    self.wrote.truncate(level);
                    self.rest_of.truncate(level);
                }
            }
            _ => {}
        }
    }

    /// Which field of `ctor` is the rest, where it is a step of a number or
    /// a sequence.
    fn recursive(&self, ctor: super::CtorId) -> Option<usize> {
        match type_shape(self.program, self.program.ctor(ctor).owner) {
            TypeShape::Natural {
                push, recursive, ..
            }
            | TypeShape::Sequence {
                push, recursive, ..
            }
            | TypeShape::Spine {
                push, recursive, ..
            } if push == ctor => Some(recursive),
            _ => None,
        }
    }

    /// Whether `atom` was written as parameter `counter` and one, summed or
    /// as its successor.
    fn stepped(&self, atom: Atom, counter: usize) -> bool {
        let is = |atom: &Atom, local: usize| atom.0.index() == local;
        let Some(Some(wrote)) = self.wrote.get(atom.0.index()) else {
            return false;
        };
        match self.program.expr(*wrote) {
            Expr::Con(ctor, fields) => {
                self.recursive(ctor).is_some()
                    && matches!(self.program.atoms(fields), [only] if is(only, counter))
            }
            Expr::Call(called, args) => {
                self.operations.get(called.index()).copied().flatten() == Some(Operation::Add)
                    && match self.program.atoms(args) {
                        [a, b] => {
                            (is(a, counter) && self.one(*b)) || (is(b, counter) && self.one(*a))
                        }
                        _ => false,
                    }
            }
            _ => false,
        }
    }

    /// Whether `atom` was written as the number one.
    fn one(&self, atom: Atom) -> bool {
        let Some(Some(wrote)) = self.wrote.get(atom.0.index()) else {
            return false;
        };
        matches!(self.program.expr(*wrote), Expr::Static(value)
            if matches!(self.program.constant(value).view(),
                super::ConstantView::Natural(n) if n.try_u64() == Ok(1)))
    }
}
