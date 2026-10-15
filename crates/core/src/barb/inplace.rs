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
//! w(xs, .., built) = match xs            w'(whole, .., n) = match n
//!   empty => base(built)                   zero => base(whole)
//!   push(x, rest) =>                       step(m) =>
//!     .. e ..                                k = length(whole) - n
//!     w(rest, .., append(built, e))          match drop(whole, k)
//!                                              empty => base(whole)
//!                                              push(x, _) =>
//!                                                .. e ..
//!                                                w'(replace(whole, k, e), .., m)
//! ```
//!
//! and a call handing `w` nothing built calls `w'(xs, .., length(xs))`.
//! A buffer nothing else holds is then written where it lies, and a shared
//! one is copied once, by the first replacement: a walk that built a new
//! buffer of the same length builds none. The element is read before it is
//! replaced, and the view `drop` answers is the same buffer from further on,
//! read no more by then. Only how many are left is counted, and the one to
//! replace worked out from the length, which replacing keeps: range
//! analysis then bounds it by a length, where counting it up beside the
//! count down would ask it to relate the two.
//!
//! In-place walks compose. A step going on with what another such walk
//! made of its rest -- `kick` pairs its head with the bodies after it
//! through `map_accum`, and goes on with what that answered -- runs the
//! other on the whole with one fewer left, which starts it at the element
//! after this one and answers the whole with those replaced; this element
//! is then written into that. Walks are found to a fixed point, each after
//! any it goes on through, so chains compose too.
//!
//! Only a walk reading what it built nowhere but in appending one element
//! to it and going round with that, and reading the rest of what it walks
//! nowhere but in going round on it, is rewritten: the first is what makes
//! what it built the whole at the end, and the second what leaves the
//! buffer nothing else's to write. Fusion comes first, since a list fusion
//! never builds is better than one written in place.

use std::collections::{HashMap, HashSet};

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::{
    Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, Range, SequenceOperation, TypeId,
    TypeShape,
};

/// Rewrite every such walk, and send each call handing it nothing built to
/// its rewriting.
pub(crate) fn in_place(program: &mut Program) {
    let recognised = program.recognised().clone();
    let walks = found(program, &recognised);
    let mut operations = HashMap::new();
    let mut placings = HashMap::new();
    let mut entries = HashMap::new();
    // A walk going on with what another made of its rest was found after
    // it, so the other is written first.
    for (id, walk) in &walks {
        let Some(&ops) = operations
            .entry(walk.list)
            .or_insert_with(|| Operations::for_list(program, &recognised, walk.list))
            .as_ref()
        else {
            continue;
        };
        let inner = match walk.inner {
            Some((call, callee)) => {
                let Some(&inner) = placings.get(&callee) else {
                    continue;
                };
                Some((call, inner))
            }
            None => None,
        };
        let placed = placed(program, *id, walk, ops, inner);
        let at = (walk.walked, walk.acc, placed);
        placings.insert(*id, at);
        entries.insert(*id, (walk.acc, entry(program, *id, walk, ops, placed)));
    }
    redirect(program, &entries);
}

/// Every walk this rewrites, each after any walk it goes on with what that
/// made of its rest.
fn found(program: &Program, recognised: &Recognised) -> Vec<(FnId, Walk)> {
    let mut walks: Vec<(FnId, Walk)> = Vec::new();
    let mut known: HashMap<FnId, Known> = HashMap::new();
    // Each round takes only walks no round took, so it goes round at most
    // once for each definition: a walk whose base case does not answer
    // what it built is found once, and never becomes known.
    let mut taken: HashSet<FnId> = HashSet::new();
    loop {
        let more: Vec<_> = (0..program.functions().len())
            .map(FnId::at)
            .filter(|id| !recognised.answered(*id) && !taken.contains(id))
            .filter_map(|id| Walk::of(program, recognised, id, &known).map(|walk| (id, walk)))
            .collect();
        if more.is_empty() {
            return walks;
        }
        for (id, walk) in more {
            taken.insert(id);
            if let Some(answer) = walk.answer {
                let at = Known {
                    walked: walk.walked,
                    acc: walk.acc,
                    answer,
                };
                known.insert(id, at);
            }
            walks.push((id, walk));
        }
    }
}

/// Where a walk's answer holds what it built: its whole answer, or one
/// field of the one constructor it answers with.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Answer {
    Whole,
    Field(CtorId, usize),
}

/// A walk already found, as another going on with what it made reads it.
#[derive(Clone, Copy)]
struct Known {
    walked: usize,
    acc: usize,
    answer: Answer,
}

/// A walk this rewrites: the parameter it walks and the one it builds in,
/// of one sequence type, the expressions appending to what it built and
/// going round, and where it goes on with what another walk made of its
/// rest, that walk's call.
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
    inner: Option<(ExprId, FnId)>,
    answer: Option<Answer>,
}

impl Walk {
    fn of(
        program: &Program,
        recognised: &Recognised,
        id: FnId,
        known: &HashMap<FnId, Known>,
    ) -> Option<Self> {
        let body = program.function(id).body()?;
        let (walked, arms) = super::walk::top_match(program, body)?;
        let params = program.params(id);
        let list = params[walked];
        let (empty, push, recursive) = super::sequence::sequence(program, list)?;
        let [nil, cons] = super::walk::split_arms(program, arms, empty, push)?;
        let arity = params.len();
        // What it walks is read nowhere else, so neither arm reads it.
        if read(program, nil.body, walked) + read(program, cons.body, walked) != 0 {
            return None;
        }
        (0..arity)
            .filter(|&acc| acc != walked && params[acc] == list)
            .find_map(|acc| {
                // The walk binds the push's fields after its parameters.
                let rest = arity + recursive;
                let mut steps = Steps::new((id, walked, acc, rest, empty), recognised, known);
                let mut scope = vec![None; arity + 2];
                steps.body(program, cons.body, &mut scope);
                let (appends, rounds, inner) = steps.builds(program, cons.body)?;
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
                    inner,
                    answer: answer(program, nil.body, acc),
                })
            })
    }
}

/// Where the base case `body` answers what was built at `acc`, reading it
/// nowhere else: as its answer, or as one field of what it builds.
fn answer(program: &Program, body: Body, acc: usize) -> Option<Answer> {
    if read(program, body, acc) != 1 {
        return None;
    }
    match program.expr(body.tail) {
        Expr::Atom(atom) if atom.0.index() == acc => Some(Answer::Whole),
        Expr::Con(ctor, fields) => program
            .atoms(fields)
            .iter()
            .position(|atom| atom.0.index() == acc)
            .map(|at| Answer::Field(ctor, at)),
        _ => None,
    }
}

/// How many times `body` reads local `level`, bound before any of it.
fn read(program: &Program, body: Body, level: usize) -> usize {
    super::walk::reads(program, super::walk::within(program, body), level)
}

/// What a local of a step is, as far as rewriting it goes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Held {
    /// The nth append to what the step built.
    Append(usize),
    /// The empty sequence.
    Empty,
    /// What the nth call of a walk found already, on the rest with nothing
    /// built, answered.
    Inner(usize),
    /// A field of that answer, taken apart by a match of one arm.
    Field(usize, CtorId, usize),
}

/// What a step goes on walking: the rest, or what the nth call of another
/// walk made of it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Going {
    Rest,
    Inner(usize),
}

/// A step read with the scope of its locals: the appends to what it built,
/// the calls of walks found already on its rest, how often each local of
/// either is read where it is in scope, and its calls going round, with
/// the append each builds in and what each goes on walking.
struct Steps<'r> {
    id: FnId,
    walked: usize,
    acc: usize,
    rest: usize,
    empty: CtorId,
    recognised: &'r Recognised,
    known: &'r HashMap<FnId, Known>,
    appends: Vec<ExprId>,
    inners: Vec<(ExprId, FnId)>,
    reads: HashMap<Held, usize>,
    rounds: Vec<(ExprId, Option<usize>, Option<Going>)>,
    /// An append or a call of another walk that nothing binds.
    refused: bool,
}
impl<'r> Steps<'r> {
    /// A step of walk `id`, which walks its parameter `walked` and builds
    /// in `acc`, binding the rest at `rest`, over a list whose empty one is
    /// `empty`, before anything of it is read.
    fn new(
        (id, walked, acc, rest, empty): (FnId, usize, usize, usize, CtorId),
        recognised: &'r Recognised,
        known: &'r HashMap<FnId, Known>,
    ) -> Self {
        Self {
            id,
            walked,
            acc,
            rest,
            empty,
            recognised,
            known,
            appends: Vec::new(),
            inners: Vec::new(),
            reads: HashMap::new(),
            rounds: Vec::new(),
            refused: false,
        }
    }
}

impl Steps<'_> {
    /// Whether the step reads what it built only in appending one element
    /// to it, each read once, as what a call going round builds in; and
    /// goes round either always on the rest, reading it nowhere else, or
    /// once, on what one call of another walk made of the rest, reading
    /// that and the rest nowhere else: the appends, the calls going round,
    /// and that other call.
    #[expect(
        clippy::type_complexity,
        reason = "the three things a rewriting edits, each by where it was written"
    )]
    fn builds(
        self,
        program: &Program,
        body: Body,
    ) -> Option<(Vec<ExprId>, Vec<ExprId>, Option<(ExprId, FnId)>)> {
        let reads = |held: Held| self.reads.get(&held).copied().unwrap_or(0);
        let consumed = (0..self.appends.len()).all(|at| {
            reads(Held::Append(at)) == 1 && self.rounds.iter().any(|round| round.1 == Some(at))
        });
        let only_appended = read(program, body, self.acc) == self.appends.len();
        let rest_read = read(program, body, self.rest);
        let going: Option<Vec<Going>> = self.rounds.iter().map(|round| round.2).collect();
        let going = going?;
        let shaped = match going.as_slice() {
            [] => false,
            [Going::Inner(at)] => {
                let callee = self.inners[*at].1;
                let read_once = match self.known[&callee].answer {
                    Answer::Whole => reads(Held::Inner(*at)) == 1,
                    Answer::Field(ctor, field) => {
                        reads(Held::Inner(*at)) == 1 && reads(Held::Field(*at, ctor, field)) == 1
                    }
                };
                read_once && rest_read == 1 && self.appends.len() == 1
            }
            all => all.iter().all(|&going| going == Going::Rest) && rest_read == all.len(),
        };
        let ok = !self.refused
            && self.rounds.iter().all(|round| round.1.is_some())
            && consumed
            && only_appended
            && shaped;
        let inner = match going.as_slice() {
            [Going::Inner(at)] => Some(self.inners[*at]),
            _ => None,
        };
        ok.then(|| {
            (
                self.appends,
                self.rounds.into_iter().map(|(expr, ..)| expr).collect(),
                inner,
            )
        })
    }

    /// Read `body`, where `scope` says what each local in scope is, where
    /// it is anything.
    fn body(&mut self, program: &Program, body: Body, scope: &mut Vec<Option<Held>>) {
        let depth = scope.len();
        let bindings = program.bindings(body.bindings);
        for (at, &expr) in bindings.iter().chain([&body.tail]).enumerate() {
            let level = depth + at;
            for atom in super::walk::operands(program, expr) {
                if let Some(Some(held)) = scope.get(atom.0.index()) {
                    *self.reads.entry(*held).or_insert(0) += 1;
                }
            }
            let tail = at == bindings.len();
            let bound = self.expr(program, expr, tail, scope);
            scope.truncate(level);
            scope.push(bound);
        }
        scope.truncate(depth);
    }

    /// Read one expression at the next level `scope` binds, answering what
    /// it is, where it is anything. A tail binds nothing.
    fn expr(
        &mut self,
        program: &Program,
        expr: ExprId,
        tail: bool,
        scope: &mut Vec<Option<Held>>,
    ) -> Option<Held> {
        let held = |atom: Atom| scope.get(atom.0.index()).copied().flatten();
        match program.expr(expr) {
            Expr::Call(callee, args) if callee == self.id => {
                let args = program.atoms(args);
                let appended = match held(args[self.acc]) {
                    Some(Held::Append(at)) => Some(at),
                    _ => None,
                };
                let going = self.going(program, expr, scope);
                self.rounds.push((expr, appended, going));
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
                Some(Held::Append(self.appends.len() - 1))
            }
            Expr::Call(callee, args) if self.inner_call(program, callee, args, scope) => {
                self.refused |= tail;
                self.inners.push((expr, callee));
                Some(Held::Inner(self.inners.len() - 1))
            }
            Expr::Con(ctor, _) if ctor == self.empty => Some(Held::Empty),
            Expr::Static(value) if program.constant(value).constructor() == self.empty => {
                Some(Held::Empty)
            }
            Expr::Match(on, arms) => {
                self.arms(program, held(on), arms, scope);
                None
            }
            _ => None,
        }
    }

    /// Whether a call of `callee` with `args` is one of a walk found
    /// already, on the rest, with nothing built.
    fn inner_call(
        &self,
        program: &Program,
        callee: FnId,
        args: Range,
        scope: &[Option<Held>],
    ) -> bool {
        self.known.get(&callee).is_some_and(|inner| {
            let args = program.atoms(args);
            args[inner.walked].0.index() == self.rest
                && scope.get(args[inner.acc].0.index()).copied().flatten() == Some(Held::Empty)
        })
    }

    /// Read a match's arms, on a local that is `on`: where that is what a
    /// walk found already answered, and the match has one arm, its fields
    /// are that answer's.
    fn arms(
        &mut self,
        program: &Program,
        on: Option<Held>,
        arms: Range,
        scope: &mut Vec<Option<Held>>,
    ) {
        let level = scope.len();
        let inner = match on {
            Some(Held::Inner(at)) => Some(at),
            _ => None,
        };
        let arms = program.arms(arms);
        let one = arms.len() == 1;
        for arm in arms {
            let fields = program.fields(arm.ctor).len();
            scope.truncate(level);
            scope.extend((0..fields).map(|field| {
                inner
                    .filter(|_| one)
                    .map(|at| Held::Field(at, arm.ctor, field))
            }));
            self.body(program, arm.body, scope);
        }
        scope.truncate(level);
    }

    /// What the call going round `expr` goes on walking, where it is the
    /// rest or what a call of another walk made of it.
    fn going(&self, program: &Program, expr: ExprId, scope: &[Option<Held>]) -> Option<Going> {
        let Expr::Call(_, args) = program.expr(expr) else {
            return None;
        };
        let walked = program.atoms(args)[self.walked];
        if walked.0.index() == self.rest {
            return Some(Going::Rest);
        }
        match scope.get(walked.0.index()).copied().flatten()? {
            Held::Inner(at) => {
                (self.known[&self.inners[at].1].answer == Answer::Whole).then_some(Going::Inner(at))
            }
            Held::Field(at, ctor, field) => (self.known[&self.inners[at].1].answer
                == Answer::Field(ctor, field))
            .then_some(Going::Inner(at)),
            _ => None,
        }
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
    monus: FnId,
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
        let monus = recognised
            .operation_over(program, super::Operation::Monus, &[count, count], count)
            .unwrap_or_else(|| super::arithmetic::write_monus(program, count));
        Some(Self {
            count,
            zero,
            succ,
            length,
            monus,
            drop,
            replace,
        })
    }
}

/// `w'`: the walk `id` replacing what it walks where it lies.
///
/// Its parameters are the walk's, with the whole of what it walks for the
/// list and how many are left to replace for what it built. The one to
/// replace next is as far from the end as that: worked out from the
/// length, which replacing keeps, rather than counted, so that range
/// analysis bounds it by a length with nothing to relate.
fn placed(
    program: &mut Program,
    id: FnId,
    walk: &Walk,
    ops: Operations,
    inner: Option<(ExprId, Placing)>,
) -> FnId {
    let arity = program.params(id).len();
    let placed = declared(program, id, "place", |params| {
        params[walk.acc] = ("left".to_owned(), ops.count);
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
        inner,
    };
    let arms = [
        Arm {
            ctor: ops.zero,
            body: rewriting.base(program, arity),
        },
        Arm {
            ctor: ops.succ,
            body: rewriting.step(program, arity),
        },
    ];
    let arms = program.terms.hold_arms(&arms);
    let mut scope = Scope::at(arity);
    let left = param(walk.acc);
    let answer = copy::push(program, &mut scope, Expr::Match(left, arms));
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
    /// The call of another walk the step goes on with what it made of the
    /// rest, and that walk's rewriting.
    inner: Option<(ExprId, Placing)>,
}

/// A walk's rewriting, and where it walks and builds.
type Placing = (usize, usize, FnId);

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

    /// Where some are left: the element as far from the end as that,
    /// taken off the whole, and the walk's step on it. The step binds one
    /// fewer left at `arity`.
    fn step(&self, program: &mut Program, arity: usize) -> Body {
        let param = |at: usize| Atom(Local::at(at));
        let (whole, left, fewer) = (param(self.walk.walked), param(self.walk.acc), param(arity));
        let mut scope = Scope::at(arity + 1);
        let args = program.terms.hold_atoms(std::iter::once(whole));
        let size = copy::push(program, &mut scope, Expr::Call(self.ops.length, args));
        let args = program.terms.hold_atoms([size, left].into_iter());
        let replaced = copy::push(program, &mut scope, Expr::Call(self.ops.monus, args));
        let args = program.terms.hold_atoms([whole, replaced].into_iter());
        let from = copy::push(program, &mut scope, Expr::Call(self.ops.drop, args));
        let level = scope.level;
        let mut inner = self.locals.clone();
        inner.extend((0..2).map(|at| param(level + at)));
        let mut edit = |program: &mut Program, scope: &mut Scope, source: ExprId, expr: Expr| {
            rewritten(program, scope, self, source, expr, (whole, replaced, fewer))
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

/// An expression of the walk's step, copied into `w'`. An append to what
/// it built is the element alone, which going round writes; a call of
/// another walk on the rest, with nothing built, is its rewriting on the
/// whole, with one fewer left, which starts it at the element after this
/// one; and going round replaces the element in what it goes on with --
/// the whole, or what the other walk made of it -- and goes round as `w'`
/// with one fewer left.
fn rewritten(
    program: &mut Program,
    scope: &mut Scope,
    rewriting: &Rewriting<'_>,
    source: ExprId,
    expr: Expr,
    (whole, replaced, fewer): (Atom, Atom, Atom),
) -> Expr {
    let walk = rewriting.walk;
    let Expr::Call(_, args) = expr else {
        return expr;
    };
    let mut going = program.atoms(args).to_vec();
    if walk.appends.contains(&source) {
        return Expr::Atom(going[1]);
    }
    if let Some((call, (walked, acc, placed))) = rewriting.inner
        && call == source
    {
        going[walked] = whole;
        going[acc] = fewer;
        return Expr::Call(placed, program.terms.hold_atoms(going.into_iter()));
    }
    if !walk.rounds.contains(&source) {
        return expr;
    }
    let onto = if rewriting.inner.is_some() {
        going[walk.walked]
    } else {
        whole
    };
    let args = program
        .terms
        .hold_atoms([onto, replaced, going[walk.acc]].into_iter());
    let written = copy::push(program, scope, Expr::Call(rewriting.ops.replace, args));
    going[walk.walked] = written;
    going[walk.acc] = fewer;
    Expr::Call(
        rewriting.placed,
        program.terms.hold_atoms(going.into_iter()),
    )
}

/// `w` called with nothing built: `w'` on the whole, all of it left. Its
/// parameters are `w`'s, so a call is sent to it as it stands.
fn entry(program: &mut Program, id: FnId, walk: &Walk, ops: Operations, placed: FnId) -> FnId {
    let entry = declared(program, id, "enter", |_| {});
    program.define(entry, |b, args| {
        let left = b.call(ops.length, &[args[walk.walked]]);
        let mut going = args.to_vec();
        going[walk.acc] = left;
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
