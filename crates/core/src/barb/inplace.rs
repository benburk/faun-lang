//! Walks building a list of what they walk, element for element, written
//! over what they walk.
//!
//! A walk built front to back, as [`super::forward`] writes `map`, appends
//! one element to what it has built for each element it takes off what it
//! walks. Where every element it appends is of the type of those it walks,
//! what it builds is what it walks with each element replaced, so it may
//! as well replace them where they are:
//!
//! ```text
//! w(xs, .., built) = match xs            w'(whole, k, .., n) = match n
//!   empty => base(built)                   zero => base(whole)
//!   push(x, rest) =>                       step(m) => match drop(whole, k)
//!     .. e ..                                empty => base(whole)
//!     w(rest, .., append(built, e))          push(x, _) =>
//!                                              .. e ..
//!                                              w'(replace(whole, k, e), k + 1, .., m)
//! ```
//!
//! and a call handing `w` nothing built calls `w'(xs, 0, .., length(xs))`.
//! A buffer nothing else holds is then written where it lies, and a shared
//! one is copied once, by the first replacement: a walk that built a new
//! buffer of the same length builds none. The element is read before it is
//! replaced, and the view `drop` answers is the same buffer from further on,
//! read no more by then. `n` counts down beside `k`, so range analysis
//! bounds `k` by the length handed in rather than leaving it unbounded.
//!
//! Only a walk reading what it built nowhere but in appending one element
//! to it and going round with that, and reading the rest of what it walks
//! nowhere but in going round on it, is rewritten: the first is what makes
//! what it built the whole at the end, and the second what leaves the
//! buffer nothing else's to write. Fusion comes first, since a list fusion
//! never builds is better than one written in place.

use std::collections::HashMap;

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::{
    Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, SequenceOperation, TypeId,
    TypeShape,
};

/// Rewrite every such walk, and send each call handing it nothing built to
/// its rewriting.
pub(crate) fn in_place(program: &mut Program) {
    let recognised = program.recognised().clone();
    let walks: Vec<_> = (0..program.functions().len())
        .map(FnId::at)
        .filter(|&id| !recognised.answered(id))
        .filter_map(|id| Walk::of(program, &recognised, id).map(|walk| (id, walk)))
        .collect();
    let mut operations = HashMap::new();
    let mut entries = HashMap::new();
    for (id, walk) in walks {
        let Some(&ops) = operations
            .entry(walk.list)
            .or_insert_with(|| Operations::for_list(program, &recognised, walk.list))
            .as_ref()
        else {
            continue;
        };
        let placed = placed(program, id, &walk, ops);
        entries.insert(id, (walk.acc, entry(program, id, &walk, ops, placed)));
    }
    redirect(program, &entries);
}

/// A walk this rewrites: the parameter it walks and the one it builds in,
/// of one sequence type, and the expressions appending to what it built
/// and going round.
struct Walk {
    list: TypeId,
    walked: usize,
    acc: usize,
    empty: CtorId,
    push: CtorId,
    nil: Arm,
    cons: Arm,
    appends: Vec<ExprId>,
    rounds: Vec<ExprId>,
}

impl Walk {
    fn of(program: &Program, recognised: &Recognised, id: FnId) -> Option<Self> {
        let body = program.function(id).body()?;
        let (walked, arms) = super::walk::top_match(program, body)?;
        let params = program.params(id);
        let list = params[walked];
        let (empty, push, recursive) = super::sequence::sequence(program, list)?;
        let [nil, cons] = super::walk::split_arms(program, arms, empty, push)?;
        let arity = params.len();
        // The walk binds the push's fields after its parameters.
        let rest = arity + recursive;
        // What it walks is read nowhere else, so neither arm reads it.
        if read(program, nil.body, walked) + read(program, cons.body, walked) != 0 {
            return None;
        }
        (0..arity)
            .filter(|&acc| acc != walked && params[acc] == list)
            .find_map(|acc| {
                let (appends, rounds) = builds(
                    program,
                    recognised,
                    (id, cons.body, arity + 2),
                    (walked, acc, rest),
                )?;
                Some(Self {
                    list,
                    walked,
                    acc,
                    empty,
                    push,
                    nil,
                    cons,
                    appends,
                    rounds,
                })
            })
    }
}

/// How many times `body` reads local `level`, bound before any of it.
fn read(program: &Program, body: Body, level: usize) -> usize {
    super::walk::reads(program, super::walk::within(program, body), level)
}

/// Where the step `body` of walk `id`, whose first binding takes `base`,
/// reads what it built at `acc` only in appending one element to it, read
/// only in going round, and the rest at `rest` only in going round on it:
/// the appends, and the calls going round.
fn builds(
    program: &Program,
    recognised: &Recognised,
    (id, body, base): (FnId, Body, usize),
    (walked, acc, rest): (usize, usize, usize),
) -> Option<(Vec<ExprId>, Vec<ExprId>)> {
    let mut steps = Steps {
        id,
        acc,
        recognised,
        appends: Vec::new(),
        reads: Vec::new(),
        rounds: Vec::new(),
        refused: false,
    };
    let mut scope = vec![None; base];
    steps.body(program, body, &mut scope);
    // Every append is read once, by a call going round on the rest; every
    // reading of what it built and of the rest is one of those.
    let rounds_ok = steps
        .rounds
        .iter()
        .all(|&(_, ref args, appended)| args[walked].0.index() == rest && appended.is_some());
    let consumed = (0..steps.appends.len())
        .all(|at| steps.reads[at] == 1 && steps.rounds.iter().any(|round| round.2 == Some(at)));
    let only_appended = read(program, body, acc) == steps.appends.len();
    let rest_read = read(program, body, rest) == steps.rounds.len();
    let ok = !steps.refused
        && !steps.rounds.is_empty()
        && rounds_ok
        && consumed
        && only_appended
        && rest_read;
    ok.then(|| {
        (
            steps.appends,
            steps.rounds.into_iter().map(|(expr, ..)| expr).collect(),
        )
    })
}

/// A step read with the scope of its locals: the appends to what it built,
/// how often each is read where it is in scope, and its calls going round,
/// with their operands and the append each builds in.
struct Steps<'r> {
    id: FnId,
    acc: usize,
    recognised: &'r Recognised,
    appends: Vec<ExprId>,
    reads: Vec<usize>,
    rounds: Vec<(ExprId, Vec<Atom>, Option<usize>)>,
    /// An append something other than a binding answers, which nothing goes
    /// round with.
    refused: bool,
}

impl Steps<'_> {
    /// Read one expression at the next level `scope` binds, answering which
    /// append it is, where it is one. A tail binds nothing.
    fn expr(
        &mut self,
        program: &Program,
        expr: ExprId,
        tail: bool,
        scope: &mut Vec<Option<usize>>,
    ) -> Option<usize> {
        let level = scope.len();
        match program.expr(expr) {
            Expr::Call(callee, args) if callee == self.id => {
                let args = program.atoms(args).to_vec();
                let appended = scope.get(args[self.acc].0.index()).copied().flatten();
                self.rounds.push((expr, args, appended));
                None
            }
            Expr::Call(callee, args)
                if self.recognised.sequences[callee.index()] == Some(SequenceOperation::Append)
                    && program.atoms(args)[0].0.index() == self.acc =>
            {
                // An append answering the step outright is read by no
                // call going round.
                self.refused |= tail;
                self.appends.push(expr);
                self.reads.push(0);
                Some(self.appends.len() - 1)
            }
            Expr::Match(_, arms) => {
                for arm in program.arms(arms) {
                    let fields = program.fields(arm.ctor).len();
                    scope.truncate(level);
                    scope.extend(std::iter::repeat_n(None, fields));
                    self.body(program, arm.body, scope);
                }
                scope.truncate(level);
                None
            }
            _ => None,
        }
    }

    /// Read `body`, where `scope` says, for each level in scope, which
    /// append it is, if one.
    fn body(&mut self, program: &Program, body: Body, scope: &mut Vec<Option<usize>>) {
        let depth = scope.len();
        let bindings = program.bindings(body.bindings);
        for (at, &expr) in bindings.iter().chain([&body.tail]).enumerate() {
            let level = depth + at;
            for atom in super::walk::operands(program, expr) {
                if let Some(Some(append)) = scope.get(atom.0.index()) {
                    self.reads[*append] += 1;
                }
            }
            let tail = at == bindings.len();
            let bound = self.expr(program, expr, tail, scope);
            scope.truncate(level);
            scope.push(bound);
        }
        scope.truncate(depth);
    }
}

/// The recognized operations a rewritten walk over one sequence type
/// calls, all counting in one natural type: found, or written.
#[derive(Clone, Copy)]
struct Operations {
    count: TypeId,
    zero: CtorId,
    succ: CtorId,
    length: FnId,
    drop: FnId,
    replace: FnId,
}

impl Operations {
    fn for_list(program: &mut Program, recognised: &Recognised, list: TypeId) -> Option<Self> {
        let (_, push, recursive) = super::sequence::sequence(program, list)?;
        let element = program.fields(push)[1 - recursive];
        // The count a length of it already answers in, or any natural.
        let found = recognised.sequence_over(program, SequenceOperation::Length, &[list]);
        let count = match found {
            Some(length) => program.function(length).result,
            None => (0..program.types().len())
                .map(TypeId::at)
                .find(|&ty| matches!(super::type_shape(program, ty), TypeShape::Natural { .. }))?,
        };
        let TypeShape::Natural {
            empty: zero,
            push: succ,
            ..
        } = super::type_shape(program, count)
        else {
            return None;
        };
        let length = found.unwrap_or_else(|| super::sequence::write_length(program, list, count));
        let drop = recognised
            .sequence_over(program, SequenceOperation::Drop, &[list, count])
            .unwrap_or_else(|| super::sequence::write_drop(program, list, count));
        let replace = recognised
            .sequence_over(program, SequenceOperation::Replace, &[list, count, element])
            .unwrap_or_else(|| super::sequence::write_replace(program, list, count));
        Some(Self {
            count,
            zero,
            succ,
            length,
            drop,
            replace,
        })
    }
}

/// `w'`: the walk `id` replacing what it walks where it lies.
///
/// Its parameters are the walk's, with the whole of what it walks for the
/// list, the count already replaced for what it built, and how many are
/// left to replace after them.
fn placed(program: &mut Program, id: FnId, walk: &Walk, ops: Operations) -> FnId {
    let arity = program.params(id).len();
    let placed = declared(program, id, "place", |params| {
        params[walk.acc] = ("replaced".to_owned(), ops.count);
        params.push(("left".to_owned(), ops.count));
    });
    let param = |at: usize| Atom(Local::at(at));
    // Each local of the walk's own, where the rewriting has it: what it
    // built is the whole, by the time either reads it.
    let mut locals: Vec<_> = (0..arity).map(param).collect();
    locals[walk.acc] = param(walk.walked);
    let rewriting = Rewriting {
        walk,
        ops,
        placed,
        locals,
    };
    let arms = [
        Arm {
            ctor: ops.zero,
            body: rewriting.base(program, arity + 1),
        },
        Arm {
            ctor: ops.succ,
            body: rewriting.step(program, arity),
        },
    ];
    let arms = program.terms.hold_arms(&arms);
    let mut scope = Scope::at(arity + 1);
    let answer = copy::push(program, &mut scope, Expr::Match(param(arity), arms));
    let body = copy::close(program, scope, answer);
    program.replace_bodies(vec![(placed, body)]);
    placed
}

/// A definition declared beside `id`, named after it with `suffix`, taking
/// its parameters as `edit` leaves them and answering what it answers.
fn declared(
    program: &mut Program,
    id: FnId,
    suffix: &str,
    edit: impl FnOnce(&mut Vec<(String, TypeId)>),
) -> FnId {
    let mut params: Vec<(String, TypeId)> = program
        .parameter_names(id)
        .map(str::to_owned)
        .zip(program.params(id).to_vec())
        .collect();
    edit(&mut params);
    let named: Vec<_> = params
        .iter()
        .map(|(name, ty)| (name.as_str(), *ty))
        .collect();
    let function = program.function(id);
    let (name, result) = (function.name, function.result);
    let name = format!("{}.{suffix}", program.name(name));
    program.declare_named(&name, &named, result)
}

/// The walk being written again as `placed`, and where `placed` has each
/// local of the walk's own.
struct Rewriting<'w> {
    walk: &'w Walk,
    ops: Operations,
    placed: FnId,
    locals: Vec<Atom>,
}

impl Rewriting<'_> {
    /// The walk's base case, whose first binding takes `level`.
    fn base(&self, program: &mut Program, level: usize) -> Body {
        copy::body(
            program,
            self.walk.nil.body,
            self.locals.clone(),
            level,
            None,
        )
    }

    /// Where some are left: the element `replaced` reaches, taken off the
    /// whole, and the walk's step on it. `left` is at `arity`, and the one
    /// fewer left the step binds after it.
    fn step(&self, program: &mut Program, arity: usize) -> Body {
        let param = |at: usize| Atom(Local::at(at));
        let (whole, replaced, fewer) = (
            param(self.walk.walked),
            param(self.walk.acc),
            param(arity + 1),
        );
        let mut scope = Scope::at(arity + 2);
        let args = program.terms.hold_atoms(std::iter::once(replaced));
        let next = copy::push(program, &mut scope, Expr::Con(self.ops.succ, args));
        let args = program.terms.hold_atoms([whole, replaced].into_iter());
        let from = copy::push(program, &mut scope, Expr::Call(self.ops.drop, args));
        let level = scope.level;
        let mut inner = self.locals.clone();
        inner.extend((0..2).map(|at| param(level + at)));
        let mut edit = |program: &mut Program, source: ExprId, expr: Expr| {
            rewritten(program, self, source, expr, (replaced, next, fewer))
        };
        let taken = copy::body(
            program,
            self.walk.cons.body,
            inner,
            level + 2,
            Some(&mut edit),
        );
        let arms = [
            Arm {
                ctor: self.walk.empty,
                body: self.base(program, level),
            },
            Arm {
                ctor: self.walk.push,
                body: taken,
            },
        ];
        let arms = program.terms.hold_arms(&arms);
        let answer = copy::push(program, &mut scope, Expr::Match(from, arms));
        copy::close(program, scope, answer)
    }
}

/// An expression of the walk's step, copied into `w'`: an append to what
/// it built replaces the element instead, and going round goes round as
/// `w'`, on the whole so far, one more replaced and one fewer left.
fn rewritten(
    program: &mut Program,
    rewriting: &Rewriting<'_>,
    source: ExprId,
    expr: Expr,
    (replaced, next, fewer): (Atom, Atom, Atom),
) -> Expr {
    let walk = rewriting.walk;
    match expr {
        Expr::Call(_, args) if walk.appends.contains(&source) => {
            let &[whole, element] = program.atoms(args) else {
                unreachable!("an append takes a sequence and an element");
            };
            let args = program
                .terms
                .hold_atoms([whole, replaced, element].into_iter());
            Expr::Call(rewriting.ops.replace, args)
        }
        Expr::Call(_, args) if walk.rounds.contains(&source) => {
            let mut going = program.atoms(args).to_vec();
            going[walk.walked] = going[walk.acc];
            going[walk.acc] = next;
            going.push(fewer);
            Expr::Call(
                rewriting.placed,
                program.terms.hold_atoms(going.into_iter()),
            )
        }
        other => other,
    }
}

/// `w` called with nothing built: `w'` on the whole, nothing replaced, and
/// all of it left. Its parameters are `w`'s, so a call is sent to it as it
/// stands.
fn entry(program: &mut Program, id: FnId, walk: &Walk, ops: Operations, placed: FnId) -> FnId {
    let entry = declared(program, id, "enter", |_| {});
    let zero = program
        .intern_number(ops.count, 0)
        .expect("a count is a natural");
    program.define(entry, |b, args| {
        let whole = args[walk.walked];
        let left = b.call(ops.length, &[whole]);
        let none = b.known(zero);
        let mut going = args.to_vec();
        going[walk.acc] = none;
        going.push(left);
        b.call(placed, &going)
    });
    entry
}

/// Send each call of a rewritten walk handing it nothing built to its
/// entry, in place.
fn redirect(program: &mut Program, entries: &HashMap<FnId, (usize, FnId)>) {
    if entries.is_empty() {
        return;
    }
    let mut calls = Vec::new();
    for at in 0..program.functions().len() {
        let Some(body) = program.function(FnId::at(at)).body() else {
            continue;
        };
        let params = program.params(FnId::at(at)).len();
        let mut written = vec![None; params];
        handed_nothing(program, entries, body, &mut written, &mut calls);
    }
    for (expr, entry) in calls {
        let Expr::Call(_, args) = program.expr(expr) else {
            unreachable!("a call found");
        };
        program.write(expr, Expr::Call(entry, args));
    }
}

/// Every call in `body` of a rewritten walk whose operand for what it
/// built was written as the empty sequence, and the entry to send it to.
/// `written` says what wrote each local so far, where a binding did.
fn handed_nothing(
    program: &Program,
    entries: &HashMap<FnId, (usize, FnId)>,
    body: Body,
    written: &mut Vec<Option<ExprId>>,
    calls: &mut Vec<(ExprId, FnId)>,
) {
    let depth = written.len();
    for &expr in program.bindings(body.bindings).iter().chain([&body.tail]) {
        match program.expr(expr) {
            Expr::Call(callee, args) => {
                if let Some(&(acc, entry)) = entries.get(&callee) {
                    let handed = program.atoms(args)[acc];
                    let empty = written[handed.0.index()].is_some_and(|wrote| {
                        let ty = program.params(callee)[acc];
                        let Some((nil, _, _)) = super::sequence::sequence(program, ty) else {
                            return false;
                        };
                        match program.expr(wrote) {
                            Expr::Con(ctor, _) => ctor == nil,
                            Expr::Static(value) => program.constant(value).constructor() == nil,
                            _ => false,
                        }
                    });
                    if empty {
                        calls.push((expr, entry));
                    }
                }
            }
            Expr::Match(_, arms) => {
                for arm in program.arms(arms) {
                    let fields = program.fields(arm.ctor).len();
                    written.extend(std::iter::repeat_n(None, fields));
                    handed_nothing(program, entries, arm.body, written, calls);
                    written.truncate(written.len() - fields);
                }
            }
            _ => {}
        }
        written.push(Some(expr));
    }
    written.truncate(depth);
}
