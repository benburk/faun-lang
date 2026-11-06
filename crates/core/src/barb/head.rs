//! A list read only for its first element, built only as far as that.
//!
//! A definition building a list by joining what its own calls answer --
//! every solution of a search, the first branch's before the second's --
//! makes every element even where its caller asks only for the first:
//!
//! ```text
//! s(..) = ...; a = s(..); b = s(..); join(a, b)
//! r = s(..); match r { empty => .., push(x, _) => .. x .. }
//! ```
//!
//! Where a call's answer is read once, by a match whose step never reads
//! the rest, only its first element matters, and the call goes to a copy of
//! the definition answering a list with that same first element and as
//! little else as it can. In the copy, a join tries the first list before
//! anything the second needs is worked out:
//!
//! ```text
//! s.head(..) = ...; a = s.head(..); match a { empty => (b = s.head(..); b), push(_, _) => a }
//! ```
//!
//! so a search asked for its first solution stops at the first it finds.
//! In the copy, a call of the definition itself goes to the copy, and an
//! element pushed onto a rest is pushed onto nothing, the rest unread.
//!
//! The answer may be read once by a walk over it instead, the copy then
//! answering for the walk. A fold, appending to an accumulator handed
//! nothing, `filter` or `map` written front to back, is read for its first
//! element: walking a join from nothing is walking the second list from
//! what walking the first left, and that keeps whatever first element it
//! has, so where the first list's walk answers an element, that is the
//! answer's. A search, which answers on the empty list a value of one
//! constructor and on a step either goes on with the rest or answers a
//! value of another, as `find`, `any` and `all` do, answers a join with
//! what it answers on the first list, or where that found nothing, what it
//! answers on the second. The copy, named for both definitions, takes the
//! walk's other parameters after the definition's own, walks each list it
//! does not join, and tries the first list's walk before the second's.
//!
//! Nothing is recognized by name: a join is the sequence operation putting
//! one list before another, an append the one putting an element after a
//! list, and the reading match and the walks are shapes. Only definitions
//! reaching no bodyless call are copied or walked, since what the copy
//! skips is work nothing may observe ([`Program::pure`]), and only one
//! whose answer some join makes in tail position, which is where there is
//! work to skip.
//!
//! [`Program::pure`]: super::calls::pure

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::walk;
use super::{
    Arm, Atom, Body, CtorId, Expr, ExprId, FnId, Local, Program, SequenceOperation, TypeId,
};

/// Give each call read only for its first element, or by a walk that needs
/// no more, a copy of what it calls that builds no more than that.
pub(crate) fn heads(program: &mut Program) {
    let recognised = program.recognised().clone();
    let pure = super::calls::pure(program, &recognised);
    let count = program.functions().len();
    let found = found(program, &recognised, &pure);
    if found.sites.is_empty() {
        return;
    }
    let mut wanted: Vec<(FnId, Reader)> = found
        .sites
        .values()
        .map(|site| (site.producer, site.reader))
        .collect();
    wanted.sort_by_key(|(id, reader)| (id.index(), reader.order()));
    wanted.dedup();
    let copies = declared(program, &wanted);
    let rewrite = Rewrite {
        recognised: &recognised,
        sites: &found.sites,
        feeding: &found.feeding,
        copies: &copies,
        fed: RefCell::new(HashMap::new()),
    };
    let mut bodies: Vec<_> = wanted
        .iter()
        .map(|&(producer, reader)| {
            let copy = copies[&(producer, reader)];
            let head = Head::of(
                program,
                (producer, copy),
                found.producers[&producer].expect("a producer is wanted only where it is one"),
                reader,
            );
            (copy, rewrite.copy_of(program, &head))
        })
        .collect();
    bodies.extend(redirected(program, &rewrite, count));
    program.replace_bodies(bodies);
}

/// Each of the first `count` definitions holding a site, copied with each
/// site calling its copy.
fn redirected(program: &mut Program, rewrite: &Rewrite<'_>, count: usize) -> Vec<(FnId, Body)> {
    let mut bodies = Vec::new();
    for id in (0..count).map(FnId::at) {
        let Some(body) = program.function(id).body() else {
            continue;
        };
        if walk::within(program, body).any(|expr| rewrite.sites.contains_key(&expr)) {
            let arity = program.params(id).len();
            let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
            let mut redirect = rewrite.redirect();
            let copied = copy::body(program, body, locals, arity, Some(&mut redirect));
            bodies.push((id, copied));
        }
    }
    bodies
}

/// A copy of each of `wanted`, declared: a copy answering the list itself
/// named with `.head` after its definition, one answering a walk named for
/// both, joined by `+`, taking the walk's other parameters after its own.
fn declared(program: &mut Program, wanted: &[(FnId, Reader)]) -> HashMap<(FnId, Reader), FnId> {
    wanted
        .iter()
        .map(|&(producer, reader)| {
            let own = program.name(program.function(producer).name).to_owned();
            let mut params = program.params(producer).to_vec();
            let (name, result) = reader.walker().map_or_else(
                || (format!("{own}.head"), program.function(producer).result),
                |walker| {
                    let walk = program.function(walker.walk);
                    let walk_params = program.params(walker.walk);
                    params.extend(reader.kept(walk_params.len()).map(|at| walk_params[at]));
                    (format!("{own}+{}", program.name(walk.name)), walk.result)
                },
            );
            ((producer, reader), program.declare(&name, &params, result))
        })
        .collect()
}

/// What finding the sites found.
struct Found {
    /// Each call to send to a copy, by the expression it is.
    sites: HashMap<ExprId, Site>,
    /// The calls of a definition a site's walk reads, whose arguments the
    /// copy is handed instead.
    feeding: HashSet<ExprId>,
    /// Each definition asked about, and its shape where it is a producer.
    producers: HashMap<FnId, Option<Shape>>,
}

/// Each call read only for its first element, or by a walk needing no
/// more, with what it calls.
fn found(program: &Program, recognised: &Recognised, pure: &[bool]) -> Found {
    let mut finder = Finder {
        program,
        recognised,
        pure,
        producers: HashMap::new(),
        walkers: HashMap::new(),
        sites: HashMap::new(),
        feeding: HashSet::new(),
    };
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        if recognised.answered(id) {
            continue;
        }
        if let Some(body) = program.function(id).body() {
            finder.find(body, program.params(id).len());
        }
    }
    Found {
        sites: finder.sites,
        feeding: finder.feeding,
        producers: finder.producers,
    }
}

/// What a list-building definition builds: its empty list, its step, and
/// which of the step's fields is the rest.
#[derive(Clone, Copy)]
struct Shape {
    empty: CtorId,
    push: CtorId,
    recursive: usize,
}

/// How a site reads what a definition answers, which the copy answers for.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Reader {
    /// The list itself, only for its first element.
    Head,
    /// A fold walking it from an empty accumulator, only for the first
    /// element the fold answers.
    Fold(Walker),
    /// A search walking it, answering at the first element it settles on.
    Search(Walker),
}

/// A walk over a list: the definition, the parameter that is the list,
/// and the accumulator a fold starts empty, `None` for a search.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Walker {
    walk: FnId,
    list: usize,
    acc: Option<usize>,
}

impl Reader {
    const fn walker(self) -> Option<Walker> {
        match self {
            Self::Head => None,
            Self::Fold(walker) | Self::Search(walker) => Some(walker),
        }
    }

    /// Of a walk taking `arity` parameters, those its copy is handed: all
    /// but the list and a fold's accumulator, which the copy makes.
    fn kept(self, arity: usize) -> impl Iterator<Item = usize> {
        let walker = self.walker();
        (0..arity).filter(move |&at| {
            walker.is_some_and(|walker| at != walker.list && Some(at) != walker.acc)
        })
    }

    /// An order among the readers of one definition, to sort them by.
    fn order(self) -> (u8, usize, usize) {
        match self {
            Self::Head => (0, 0, 0),
            Self::Fold(walker) => (1, walker.walk.index(), walker.list),
            Self::Search(walker) => (2, walker.walk.index(), walker.list),
        }
    }
}

/// A call to send to a copy: what it calls, how its answer is read, and,
/// where a walk reads it, the call of the definition the walk reads.
#[derive(Clone, Copy)]
struct Site {
    producer: FnId,
    reader: Reader,
    feed: Option<ExprId>,
}

/// A definition being copied, and the copy it is becoming.
struct Head {
    producer: FnId,
    copy: FnId,
    shape: Shape,
    reader: Reader,
    /// What the copy answers, and the constructor of it that says the first
    /// list gave nothing, so the second is tried.
    answer: TypeId,
    nothing: CtorId,
    /// The walk's parameters the copy is handed, after its definition's own.
    kept: Vec<Atom>,
}

impl Head {
    fn of(program: &Program, (producer, copy): (FnId, FnId), shape: Shape, reader: Reader) -> Self {
        let arity = program.params(producer).len();
        let total = program.params(copy).len();
        let answer = program.function(copy).result;
        let nothing = match reader {
            Reader::Head | Reader::Fold(_) => {
                super::sequence::sequence(program, answer)
                    .expect("a fold answers a list")
                    .0
            }
            Reader::Search(walker) => searched_nothing(program, walker.walk, walker.list)
                .expect("a search answers one constructor on the empty list"),
        };
        Self {
            producer,
            copy,
            shape,
            reader,
            answer,
            nothing,
            kept: (arity..total).map(|at| Atom(Local::at(at))).collect(),
        }
    }
}

/// Finding the calls read only for their first element.
struct Finder<'a> {
    program: &'a Program,
    recognised: &'a Recognised,
    pure: &'a [bool],
    /// Each definition asked about, and its shape where it is a producer.
    producers: HashMap<FnId, Option<Shape>>,
    /// Each walk asked about, with the parameter it walks, and how it reads
    /// it where it is a fold or a search.
    walkers: HashMap<(FnId, usize), Option<Reader>>,
    sites: HashMap<ExprId, Site>,
    feeding: HashSet<ExprId>,
}

impl Finder<'_> {
    /// Find the sites in `body`, whose first binding takes `base`, and in
    /// every arm it holds.
    fn find(&mut self, body: Body, base: usize) {
        let mut exprs = self.program.bindings(body.bindings).to_vec();
        exprs.push(body.tail);
        for (at, &id) in exprs.iter().enumerate() {
            let level = base + at;
            match self.program.expr(id) {
                Expr::Call(callee, _) if at + 1 < exprs.len() => {
                    let Some(shape) = self.producer(callee) else {
                        continue;
                    };
                    if self.read_for_head(&exprs[at + 1..], level, shape) {
                        let site = Site {
                            producer: callee,
                            reader: Reader::Head,
                            feed: None,
                        };
                        self.sites.insert(id, site);
                    } else if let Some((walked, reader)) = self.walked(&exprs, base, at) {
                        let site = Site {
                            producer: callee,
                            reader,
                            feed: Some(id),
                        };
                        self.sites.insert(walked, site);
                        self.feeding.insert(id);
                    }
                }
                Expr::Match(_, arms) => {
                    for arm in self.program.arms(arms) {
                        let fields = self.program.fields(arm.ctor).len();
                        self.find(arm.body, level + fields);
                    }
                }
                _ => {}
            }
        }
    }

    /// Whether `id` builds a list that a join answers somewhere in tail
    /// position, and may be copied: it reaches no bodyless call and is not
    /// answered as an operation it was recognized as.
    fn producer(&mut self, id: FnId) -> Option<Shape> {
        if let Some(&known) = self.producers.get(&id) {
            return known;
        }
        let found = self.find_producer(id);
        self.producers.insert(id, found);
        found
    }

    fn find_producer(&self, id: FnId) -> Option<Shape> {
        if !self.takes_part(id) {
            return None;
        }
        let body = self.program.function(id).body()?;
        let (empty, push, recursive) =
            super::sequence::sequence(self.program, self.program.function(id).result)?;
        self.joins_in_tail(body).then_some(Shape {
            empty,
            push,
            recursive,
        })
    }

    /// Whether `id` reaches no bodyless call and is not answered as an
    /// operation it was recognized as.
    fn takes_part(&self, id: FnId) -> bool {
        self.pure.get(id.index()).copied().unwrap_or(false) && !self.recognised.answered(id)
    }

    /// Whether a join answers `body`, or an arm of a match answering it.
    fn joins_in_tail(&self, body: Body) -> bool {
        match self.program.expr(body.tail) {
            Expr::Call(callee, _) => joins(self.recognised, callee),
            Expr::Match(_, arms) => self
                .program
                .arms(arms)
                .iter()
                .any(|arm| self.joins_in_tail(arm.body)),
            Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => false,
        }
    }

    /// Whether the local at `level` is read by `later`, the expressions of
    /// its body after it, only as what matches of it take apart, and none
    /// of those reads the rest. Inlining a test and a negation of it leaves
    /// two such matches, one read by nothing.
    fn read_for_head(&self, later: &[ExprId], level: usize, shape: Shape) -> bool {
        let reads = walk::reads(
            self.program,
            walk::nested(self.program, later.iter().copied()),
            level,
        );
        let mut matched = 0;
        for (at, &id) in later.iter().enumerate() {
            let Expr::Match(Atom(on), arms) = self.program.expr(id) else {
                continue;
            };
            if on.index() != level {
                continue;
            }
            let Some([_, step]) = walk::split_arms(self.program, arms, shape.empty, shape.push)
            else {
                return false;
            };
            // The match binds its fields from its own level, the next after
            // `level` that it is the `at`th of.
            let rest = level + 1 + at + shape.recursive;
            if walk::reads(self.program, walk::within(self.program, step.body), rest) != 0 {
                return false;
            }
            matched += 1;
        }
        matched > 0 && reads == matched
    }

    /// Where the answer `exprs[at]` binds is read once, by a call of a walk
    /// that needs no more of it than its first element, that call and how
    /// the walk reads it. Its body's first binding takes `base`.
    fn walked(&mut self, exprs: &[ExprId], base: usize, at: usize) -> Option<(ExprId, Reader)> {
        let level = base + at;
        let later = &exprs[at + 1..];
        let reads = walk::reads(
            self.program,
            walk::nested(self.program, later.iter().copied()),
            level,
        );
        if reads != 1 {
            return None;
        }
        let (by, &call) = later.iter().enumerate().find(|&(_, &id)| {
            matches!(self.program.expr(id), Expr::Call(_, args)
                if self.program.atoms(args).iter().any(|atom| atom.0.index() == level))
        })?;
        let Expr::Call(walk, args) = self.program.expr(call) else {
            return None;
        };
        let args = self.program.atoms(args);
        let list = args.iter().position(|atom| atom.0.index() == level)?;
        let reader = self.walker(walk, list)?;
        let fits = match reader {
            Reader::Fold(walker) => {
                let acc = walker.acc.expect("a fold has an accumulator");
                let shape = Shape::of(self.program, self.program.function(walk).result)?;
                // The walk's call is the `by`th expression after `at`.
                let call_level = level + 1 + by;
                self.empty_at(exprs, base, args[acc], shape.empty)
                    && self.read_for_head(&exprs[at + 1 + by + 1..], call_level, shape)
            }
            Reader::Search(_) => true,
            Reader::Head => false,
        };
        fits.then_some((call, reader))
    }

    /// Whether `atom` is bound among `exprs`, the first at `base`, to the
    /// empty list.
    fn empty_at(&self, exprs: &[ExprId], base: usize, atom: Atom, empty: CtorId) -> bool {
        let Some(&bound) = atom
            .0
            .index()
            .checked_sub(base)
            .and_then(|at| exprs.get(at))
        else {
            return false;
        };
        constructor(self.program, bound) == Some(empty)
    }

    /// How `walk` reads its parameter `list`, where it is a fold or a
    /// search that may be pushed into what builds the list.
    fn walker(&mut self, walk: FnId, list: usize) -> Option<Reader> {
        if let Some(&known) = self.walkers.get(&(walk, list)) {
            return known;
        }
        let found = if self.takes_part(walk) {
            folded(self.program, self.recognised, walk, list)
                .map(|acc| {
                    Reader::Fold(Walker {
                        walk,
                        list,
                        acc: Some(acc),
                    })
                })
                .or_else(|| {
                    searched_nothing(self.program, walk, list).map(|_| {
                        Reader::Search(Walker {
                            walk,
                            list,
                            acc: None,
                        })
                    })
                })
        } else {
            None
        };
        self.walkers.insert((walk, list), found);
        found
    }
}

impl Shape {
    fn of(program: &Program, ty: TypeId) -> Option<Self> {
        let (empty, push, recursive) = super::sequence::sequence(program, ty)?;
        Some(Self {
            empty,
            push,
            recursive,
        })
    }
}

/// The two arms of `walk`'s match on its parameter `list`, which is all its
/// body is, and the level its step's rest takes.
fn walk_arms(program: &Program, walk: FnId, list: usize) -> Option<(Arm, Arm, usize)> {
    let body = program.function(walk).body()?;
    if !program.bindings(body.bindings).is_empty() {
        return None;
    }
    let Expr::Match(Atom(on), arms) = program.expr(body.tail) else {
        return None;
    };
    let shape = Shape::of(program, *program.params(walk).get(list)?)?;
    let [empty, step] = walk::split_arms(program, arms, shape.empty, shape.push)?;
    let arity = program.params(walk).len();
    (on.index() == list).then_some((empty, step, arity + shape.recursive))
}

/// Where `walk` folds over its parameter `list` from an accumulator, the
/// accumulator: on the empty list it answers that, and every way its step
/// goes is a call of itself on the rest, its other parameters as they came
/// but the accumulator, which it hands on as it came or with an element
/// appended. The fold is then the same walked over two lists one after the
/// other as over the second from what walking the first left, and once it
/// has a first element, keeps it.
fn folded(program: &Program, recognised: &Recognised, walk: FnId, list: usize) -> Option<usize> {
    let (empty, step, rest) = walk_arms(program, walk, list)?;
    // What the empty arm binds is pure, and only its answer matters.
    let Expr::Atom(Atom(acc)) = program.expr(empty.body.tail) else {
        return None;
    };
    let acc = acc.index();
    let arity = program.params(walk).len();
    if acc >= arity || acc == list || program.params(walk)[acc] != program.function(walk).result {
        return None;
    }
    let fold = Steps {
        program,
        recognised,
        walk,
        list,
        rest,
        arity,
    };
    let fields = program.fields(step.ctor).len();
    fold.folds(step.body, arity + fields, acc, &mut HashMap::new())
        .then_some(acc)
}

/// What `walk` answers on the empty list, where it searches its parameter
/// `list`: on the empty list a value of one constructor, the one this
/// answers, and on its step either a call of itself on the rest with its
/// other parameters as they came, or a value of another constructor. It
/// then answers on two lists one after the other what it answers on the
/// first, or where that is the empty list's, on the second.
fn searched_nothing(program: &Program, walk: FnId, list: usize) -> Option<CtorId> {
    let (empty, step, rest) = walk_arms(program, walk, list)?;
    let nothing = constructor(program, empty.body.tail)?;
    let search = Steps {
        program,
        recognised: &Recognised::default(),
        walk,
        list,
        rest,
        arity: program.params(walk).len(),
    };
    let fields = program.fields(step.ctor).len();
    let level = search.arity + fields;
    search
        .searches(step.body, level, nothing, &mut HashMap::new())
        .then_some(nothing)
}

/// Reading the ways a walk's step goes.
struct Steps<'a> {
    program: &'a Program,
    recognised: &'a Recognised,
    walk: FnId,
    list: usize,
    /// The level the step's rest takes.
    rest: usize,
    arity: usize,
}

impl Steps<'_> {
    /// Whether `args`, a call's, are the walk's on the rest with every
    /// parameter but `except` as it came.
    fn goes_on(&self, args: &[Atom], except: Option<usize>) -> bool {
        args.len() == self.arity
            && args.iter().enumerate().all(|(at, atom)| {
                let level = atom.0.index();
                if at == self.list {
                    level == self.rest
                } else {
                    Some(at) == except || level == at
                }
            })
    }

    /// Whether every way `body` goes is a call of the walk going on with
    /// the accumulator `acc` as it came or with an element appended.
    /// `written` holds what each local bound before it is bound to, and its
    /// first binding takes `level`.
    fn folds(
        &self,
        body: Body,
        level: usize,
        acc: usize,
        written: &mut HashMap<usize, ExprId>,
    ) -> bool {
        for (at, &binding) in self.program.bindings(body.bindings).iter().enumerate() {
            written.insert(level + at, binding);
        }
        let level = level + self.program.bindings(body.bindings).len();
        match self.program.expr(body.tail) {
            Expr::Call(callee, args) if callee == self.walk => {
                let args = self.program.atoms(args);
                self.goes_on(args, Some(acc)) && self.appended(written, args[acc], acc)
            }
            Expr::Match(_, arms) => self.program.arms(arms).iter().all(|arm| {
                let fields = self.program.fields(arm.ctor).len();
                self.folds(arm.body, level + fields, acc, written)
            }),
            Expr::Call(..) | Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) => false,
        }
    }

    /// Whether `atom` is the accumulator `acc`, or it with an element
    /// appended.
    fn appended(&self, written: &HashMap<usize, ExprId>, atom: Atom, acc: usize) -> bool {
        let level = atom.0.index();
        if level == acc {
            return true;
        }
        let Some(&bound) = written.get(&level) else {
            return false;
        };
        let Expr::Call(callee, args) = self.program.expr(bound) else {
            return false;
        };
        self.recognised.sequences.get(callee.index()) == Some(&Some(SequenceOperation::Append))
            && self
                .program
                .atoms(args)
                .first()
                .map(|first| first.0.index())
                == Some(acc)
    }

    /// Whether every way `body` goes is a call of the walk going on with
    /// its other parameters as they came, or a value of a constructor other
    /// than `nothing`. Its first binding takes `level`.
    fn searches(
        &self,
        body: Body,
        level: usize,
        nothing: CtorId,
        written: &mut HashMap<usize, ExprId>,
    ) -> bool {
        for (at, &binding) in self.program.bindings(body.bindings).iter().enumerate() {
            written.insert(level + at, binding);
        }
        let level = level + self.program.bindings(body.bindings).len();
        let tail = body.tail;
        match self.program.expr(tail) {
            Expr::Call(callee, args) if callee == self.walk => {
                self.goes_on(self.program.atoms(args), None)
            }
            Expr::Match(_, arms) => self.program.arms(arms).iter().all(|arm| {
                let fields = self.program.fields(arm.ctor).len();
                self.searches(arm.body, level + fields, nothing, written)
            }),
            Expr::Atom(Atom(local)) => written
                .get(&local.index())
                .and_then(|&bound| constructor(self.program, bound))
                .is_some_and(|ctor| ctor != nothing),
            Expr::Con(..) | Expr::Static(_) => {
                constructor(self.program, tail).is_some_and(|ctor| ctor != nothing)
            }
            Expr::Call(..) => false,
        }
    }
}

/// The constructor `expr` builds, where it is a constructor applied or a
/// known value.
fn constructor(program: &Program, expr: ExprId) -> Option<CtorId> {
    match program.expr(expr) {
        Expr::Con(ctor, _) => Some(ctor),
        Expr::Static(value) => Some(program.constant(value).constructor()),
        Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => None,
    }
}

/// Copying bodies, each site calling its definition's copy.
struct Rewrite<'a> {
    recognised: &'a Recognised,
    sites: &'a HashMap<ExprId, Site>,
    feeding: &'a HashSet<ExprId>,
    copies: &'a HashMap<(FnId, Reader), FnId>,
    /// What each call a walk's site reads was last copied as, which that
    /// site's copy is called with.
    fed: RefCell<HashMap<ExprId, Vec<Atom>>>,
}

/// What a local a copy has no use for stands for, so that reading one fails
/// validation rather than reading something else.
const UNREAD: Atom = Atom(Local(u32::MAX));

impl Rewrite<'_> {
    /// An edit sending each site to its definition's copy.
    fn redirect(&self) -> impl FnMut(&mut Program, &mut Scope, ExprId, Expr) -> Expr + '_ {
        |program, _, id, expr| {
            if self.feeding.contains(&id) {
                if let Expr::Call(_, args) = expr {
                    let args = program.atoms(args).to_vec();
                    self.fed.borrow_mut().insert(id, args);
                }
                return expr;
            }
            let (Some(site), Expr::Call(_, args)) = (self.sites.get(&id), expr) else {
                return expr;
            };
            let copy = self.copies[&(site.producer, site.reader)];
            let Some(feed) = site.feed else {
                return Expr::Call(copy, args);
            };
            // A walk's site: its definition's arguments, as copied, and the
            // walk's own it hands on.
            let Some(mut handed) = self.fed.borrow().get(&feed).cloned() else {
                return expr;
            };
            let walked = program.atoms(args).to_vec();
            handed.extend(site.reader.kept(walked.len()).map(|at| walked[at]));
            Expr::Call(copy, program.terms.hold_atoms(handed.into_iter()))
        }
    }

    /// The body of the copy `head` is becoming.
    fn copy_of(&self, program: &mut Program, head: &Head) -> Body {
        let body = program
            .function(head.producer)
            .body()
            .expect("a producer has a body");
        let arity = program.params(head.producer).len();
        let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
        let mut scope = Scope::at(arity + head.kept.len());
        let answer = self.headed(program, head, body, locals, &mut scope);
        copy::close(program, scope, answer)
    }

    /// `body` copied into `scope` as the copy `head` answers it, every
    /// local it reads from before it read through `locals`.
    fn headed(
        &self,
        program: &mut Program,
        head: &Head,
        body: Body,
        mut locals: Vec<Atom>,
        scope: &mut Scope,
    ) -> Atom {
        let base = locals.len();
        let bindings = program.bindings(body.bindings).to_vec();
        if let Expr::Call(callee, args) = program.expr(body.tail)
            && joins(self.recognised, callee)
            && let &[first, then] = program.atoms(args)
        {
            return self.joined(
                program,
                head,
                (&bindings, body.tail),
                (locals, base),
                scope,
                (first, then),
            );
        }
        for &binding in &bindings {
            let value = self.copied(program, binding, &locals, scope);
            locals.push(value);
        }
        match program.expr(body.tail) {
            Expr::Match(on, arms) => {
                let mut rebuilt = Vec::new();
                for arm in program.arms(arms).to_vec() {
                    let fields = program.fields(arm.ctor).len();
                    let mut inner = locals.clone();
                    inner.extend((0..fields).map(|at| Atom(Local::at(scope.level + at))));
                    let mut arm_scope = Scope::at(scope.level + fields);
                    let answer = self.headed(program, head, arm.body, inner, &mut arm_scope);
                    rebuilt.push(Arm {
                        ctor: arm.ctor,
                        body: copy::close(program, arm_scope, answer),
                    });
                }
                let arms = program.terms.hold_arms(&rebuilt);
                copy::push(program, scope, Expr::Match(locals[on.0.index()], arms))
            }
            _ => self.headed_expr(program, head, body.tail, &locals, scope),
        }
    }

    /// A body answering `join(first, then)`: `first` as the copy answers
    /// it, and only where that gives nothing, every binding `first` does
    /// not need, then `then`.
    fn joined(
        &self,
        program: &mut Program,
        head: &Head,
        (bindings, tail): (&[ExprId], ExprId),
        (mut locals, base): (Vec<Atom>, usize),
        scope: &mut Scope,
        (first, then): (Atom, Atom),
    ) -> Atom {
        // The tail reads nothing but the two lists, so a binding the first
        // does not need is the second's, or read by nothing.
        let firsts = needs(program, bindings, base, first.0.index());
        let first_once = read_once(program, (bindings, tail), base, first.0.index());
        let then_once = read_once(program, (bindings, tail), base, then.0.index());
        for (at, &binding) in bindings.iter().enumerate() {
            let level = base + at;
            let value = if !firsts.contains(&level) {
                UNREAD
            } else if level == first.0.index() {
                self.answered(program, head, binding, (&locals, first_once), scope)
            } else {
                self.copied(program, binding, &locals, scope)
            };
            locals.push(value);
        }
        let tried = if first.0.index() < base {
            // A parameter: the copy answers for it as for any list it holds.
            leaf(program, head, locals[first.0.index()], scope)
        } else {
            locals[first.0.index()]
        };
        let moved = |level: usize| !firsts.contains(&level);
        // The arm binds what it takes apart before anything it works out.
        let after = scope.level + program.fields(head.nothing).len();
        let otherwise = self.otherwise(
            program,
            head,
            (bindings, base, &moved),
            locals,
            (then, then_once),
            after,
        );
        let arms = tried_arms(program, head, (tried, otherwise), scope.level);
        copy::push(program, scope, Expr::Match(tried, arms))
    }

    /// The body where the first list gave nothing: each binding `moved`
    /// says only the second list needs, worked out now, then the second
    /// list as the copy answers it. Its first binding takes `level`.
    fn otherwise(
        &self,
        program: &mut Program,
        head: &Head,
        (bindings, base, moved): (&[ExprId], usize, &dyn Fn(usize) -> bool),
        mut locals: Vec<Atom>,
        (then, then_once): (Atom, bool),
        level: usize,
    ) -> Body {
        let mut scope = Scope::at(level);
        for (at, &binding) in bindings.iter().enumerate() {
            let level = base + at;
            if !moved(level) {
                continue;
            }
            // Only what is bound before it: an arm it holds binds its
            // fields after the locals it is handed.
            let before = &locals[..level];
            locals[level] = if level == then.0.index() {
                self.answered(program, head, binding, (before, then_once), &mut scope)
            } else {
                self.copied(program, binding, before, &mut scope)
            };
        }
        let answer = if then.0.index() < base {
            leaf(program, head, locals[then.0.index()], &mut scope)
        } else {
            locals[then.0.index()]
        };
        copy::close(program, scope, answer)
    }

    /// A binding joined, as the copy answers it: through [`Self::headed_expr`]
    /// where nothing else reads it, and otherwise copied and walked.
    fn answered(
        &self,
        program: &mut Program,
        head: &Head,
        id: ExprId,
        (locals, once): (&[Atom], bool),
        scope: &mut Scope,
    ) -> Atom {
        if once {
            self.headed_expr(program, head, id, locals, scope)
        } else {
            let value = self.copied(program, id, locals, scope);
            leaf(program, head, value, scope)
        }
    }

    /// An expression whose answer is read only as the copy answers it: a
    /// call of the definition as a call of the copy; for its first element
    /// alone, an element pushed onto a rest as pushed onto nothing; and for
    /// a walk, any other list walked.
    fn headed_expr(
        &self,
        program: &mut Program,
        head: &Head,
        id: ExprId,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Atom {
        match program.expr(id) {
            Expr::Call(callee, args) if callee == head.producer => {
                #[expect(
                    clippy::needless_collect,
                    reason = "the atoms are read from the program the new ones are held in"
                )]
                let args: Vec<Atom> = program
                    .atoms(args)
                    .iter()
                    .map(|atom| locals[atom.0.index()])
                    .chain(head.kept.iter().copied())
                    .collect();
                let args = program.terms.hold_atoms(args.into_iter());
                copy::push(program, scope, Expr::Call(head.copy, args))
            }
            Expr::Con(ctor, fields) if ctor == head.shape.push && head.reader == Reader::Head => {
                pushed_onto_nothing(program, head, (ctor, fields), locals, scope)
            }
            _ => {
                let value = self.copied(program, id, locals, scope);
                leaf(program, head, value, scope)
            }
        }
    }

    /// An expression copied as it is, but for the sites in it.
    fn copied(
        &self,
        program: &mut Program,
        id: ExprId,
        locals: &[Atom],
        scope: &mut Scope,
    ) -> Atom {
        let mut redirect = self.redirect();
        copy::expr(program, id, locals, scope, Some(&mut redirect))
    }
}

/// A list the definition answers without joining, as the copy answers it:
/// itself for its first element, and for a walk, walked, a fold from
/// nothing.
fn leaf(program: &mut Program, head: &Head, list: Atom, scope: &mut Scope) -> Atom {
    let Some(walker) = head.reader.walker() else {
        return list;
    };
    let arity = program.params(walker.walk).len();
    let mut kept = head.kept.iter().copied();
    let mut args = Vec::with_capacity(arity);
    for at in 0..arity {
        if at == walker.list {
            args.push(list);
        } else if Some(at) == walker.acc {
            let none = program.terms.hold_atoms(std::iter::empty());
            args.push(copy::push(program, scope, Expr::Con(head.nothing, none)));
        } else {
            args.push(
                kept.next()
                    .expect("the copy is handed the walk's other parameters"),
            );
        }
    }
    let args = program.terms.hold_atoms(args.into_iter());
    copy::push(program, scope, Expr::Call(walker.walk, args))
}

/// `ctor(fields)`, the step putting an element onto a rest, as the copy for
/// its first element answers it: pushed onto nothing, the rest unread.
fn pushed_onto_nothing(
    program: &mut Program,
    head: &Head,
    (ctor, fields): (CtorId, super::Range),
    locals: &[Atom],
    scope: &mut Scope,
) -> Atom {
    let none = program.terms.hold_atoms(std::iter::empty());
    let nothing = copy::push(program, scope, Expr::Con(head.shape.empty, none));
    #[expect(
        clippy::needless_collect,
        reason = "the atoms are read from the program the new ones are held in"
    )]
    let fields: Vec<Atom> = program
        .atoms(fields)
        .iter()
        .enumerate()
        .map(|(at, atom)| {
            if at == head.shape.recursive {
                nothing
            } else {
                locals[atom.0.index()]
            }
        })
        .collect();
    let fields = program.terms.hold_atoms(fields.into_iter());
    copy::push(program, scope, Expr::Con(ctor, fields))
}

/// The arms of a match on `tried`, what the first list gave, at `level`:
/// where it gave nothing, `otherwise`, and where it gave something, that,
/// which the whole answers too.
fn tried_arms(
    program: &mut Program,
    head: &Head,
    (tried, otherwise): (Atom, Body),
    level: usize,
) -> super::Range {
    let arms: Vec<Arm> = (0..program.ctors(head.answer).len())
        .map(|tag| {
            let ctor = program.ctor_at(head.answer, u32::try_from(tag).expect("few tags"));
            let body = if ctor == head.nothing {
                otherwise
            } else {
                let fields = program.fields(ctor).len();
                copy::close(program, Scope::at(level + fields), tried)
            };
            Arm { ctor, body }
        })
        .collect();
    program.terms.hold_arms(&arms)
}

/// Whether the local at `level` is one of `bindings`, the first of which
/// takes `base`, read once by those after it and by `tail`.
fn read_once(
    program: &Program,
    (bindings, tail): (&[ExprId], ExprId),
    base: usize,
    level: usize,
) -> bool {
    let Some(at) = level.checked_sub(base).filter(|&at| at < bindings.len()) else {
        return false;
    };
    let mut after = bindings[at + 1..].to_vec();
    after.push(tail);
    walk::reads(program, walk::nested(program, after), level) == 1
}

/// Whether `id` is recognized as putting one list before another.
fn joins(recognised: &Recognised, id: FnId) -> bool {
    recognised.sequences.get(id.index()) == Some(&Some(SequenceOperation::Prepend))
}

/// The levels of `bindings` that working out `level` needs: itself where it
/// is one of them, and whatever it reads of them, however indirectly. The
/// first of `bindings` takes `base`; a binding reads only those before it,
/// so a level its arms bind for themselves is never one of them.
fn needs(program: &Program, bindings: &[ExprId], base: usize, level: usize) -> HashSet<usize> {
    let mut needed = HashSet::new();
    let mut waiting = vec![level];
    while let Some(level) = waiting.pop() {
        let Some(&binding) = level.checked_sub(base).and_then(|at| bindings.get(at)) else {
            continue;
        };
        if !needed.insert(level) {
            continue;
        }
        for id in walk::nested(program, [binding]) {
            waiting.extend(
                walk::operands(program, id)
                    .map(|atom| atom.0.index())
                    .filter(|&read| read >= base && read < level),
            );
        }
    }
    needed
}
