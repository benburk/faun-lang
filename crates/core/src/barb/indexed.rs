//! A list read only by its positions and its length, never built.
//!
//! `List.range(n).map(f)` is a walk counting `n` down while it counts a
//! position up, appending what it works out of the position each step:
//! the element at `k` is `f` of the position `k` steps on, and there are
//! `n` of them. A definition reading such a list only by its length and by
//! what [`List.drop`](super::SequenceOperation::Drop) leaves at a position,
//! taken apart at once into its first element, reads nothing but those:
//!
//! ```text
//! xs = p(start, n, [])         r(xs, i, total) = ... xs.len() ...
//! r(xs, 0, 0)                    match xs.drop(i) { [] => a; [x, *_] => b }
//! ```
//!
//! So a copy of the reader takes what the walk was handed in the list's
//! place: the length is the count, and what is left at `i` is empty where
//! `i` is not below the count, exactly as dropping past the end leaves, and
//! otherwise has at its front the element worked out where it is read,
//! by a definition taking the position. Nothing is built.
//!
//! An element is worked out where the list would have been read, never
//! more often than building the list worked it out: the reader reads one
//! position a step, a position it counts up by a known number every time it
//! goes round, or reads one at most and does not go round; and the list is
//! read by that one call, which the reader hands it on to only as itself.
//! The walk building it is pure, so working out an element later, or not at
//! all where nothing reads it, is not observable. A list stored, handed to
//! anything else, or read any other way is built as it was.

use rustc_hash::FxHashMap as HashMap;

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::split::{Handed, scoped, self_calls};
use super::{
    Arm, Atom, Body, ConstantView, CtorId, Expr, ExprId, FnId, Local, Operation, Program,
    SequenceOperation, TypeShape, type_shape, walk,
};

/// A local no copied body may read: what the list or the walk's own
/// accumulator stands for, so that reading one fails validation rather
/// than reading something else.
const UNREAD: Atom = Atom(Local(u32::MAX));

/// Send every call handing a reader of positions a list a counting walk
/// built, and nothing else reads, to a copy taking what the walk was
/// handed.
pub(crate) fn positions(program: &mut Program) {
    let recognised = program.recognised().clone();
    let pure = super::calls::pure(program, &recognised);
    let mut indexed = Indexed {
        recognised,
        pure,
        producers: HashMap::default(),
        readers: HashMap::default(),
        elements: HashMap::default(),
        copies: HashMap::default(),
        program,
    };
    let count = indexed.program.functions().len();
    let mut made: Vec<FnId> = (0..count)
        .map(FnId::at)
        .filter(|&id| indexed.rewrite(id))
        .collect();
    // Each element is worked out where it is read.
    let copies: Vec<FnId> = indexed.copies.values().copied().collect();
    super::normalize::reinline(indexed.program, &copies);
    made.extend(copies);
    made.sort_unstable();
    made.dedup();
    super::normalize::resimplify(indexed.program, &made);
}

/// A walk building a list a position at a time, as [`Indexed::producer`]
/// reads it.
#[derive(Clone)]
struct Producer {
    /// The count it takes down, and the list it appends to.
    count: usize,
    acc: usize,
    /// Which of its parameters it counts up by one each step; the rest but
    /// the count and the list it hands on as they came.
    up: Vec<bool>,
}

/// What reads a list only by its positions and length, as
/// [`Indexed::reader`] reads it.
#[derive(Clone, Copy)]
struct Reader {
    /// The definitions it calls recognized as taking a sequence's length
    /// and as dropping its first elements, where it calls them.
    length: Option<FnId>,
    drop: Option<FnId>,
}

/// The definition working out the element at a position of what a walk
/// builds: the walk's parameters but its count and list, then the position.
#[derive(Clone, Copy)]
struct Element {
    id: FnId,
}

/// What reads a list: the length and drop called, each position dropped
/// with the level its answer takes, and whether the reader goes round.
type ListReads = (Reader, Vec<(usize, Atom)>, bool);

/// What a reader's copy reads in its list's place.
struct Read {
    copy: FnId,
    /// What the walk was handed, its count and the rest.
    made: Vec<Atom>,
    count: Atom,
    kept: Vec<Atom>,
    element: Element,
    /// Less-than over positions, and its two answers.
    less: (FnId, CtorId, CtorId),
    /// The type of the list.
    item: super::TypeId,
}

impl Read {
    /// What the copy writes in place of `expr`, copied from the reader
    /// `reader` reading its list as `reads` says: going on with what the
    /// walk was handed, its count for its length, and for what dropping
    /// position `i` leaves, whether `i` is below the count, and where it
    /// is, the element worked out at `i`.
    fn rewritten(
        &self,
        program: &mut Program,
        (reader, reads): (FnId, Reader),
        dropped: &mut HashMap<usize, Atom>,
        scope: &Scope,
        expr: Expr,
    ) -> Expr {
        match expr {
            Expr::Call(callee, args) if callee == reader => {
                let args = program.atoms(args).to_vec();
                let at = args
                    .iter()
                    .position(|&atom| atom == UNREAD)
                    .expect("the list");
                let handed = handed_for(&args, at, &self.made);
                Expr::Call(self.copy, program.terms.hold_atoms(handed.into_iter()))
            }
            Expr::Call(callee, args)
                if Some(callee) == reads.length && program.atoms(args) == [UNREAD] =>
            {
                Expr::Atom(self.count)
            }
            Expr::Call(callee, args)
                if Some(callee) == reads.drop && program.atoms(args).first() == Some(&UNREAD) =>
            {
                let position = program.atoms(args)[1];
                dropped.insert(scope.level, position);
                let compared = program.terms.hold_atoms([position, self.count].into_iter());
                Expr::Call(self.less.0, compared)
            }
            Expr::Match(on, arms) if dropped.contains_key(&on.0.index()) => {
                self.found(program, on, arms, dropped[&on.0.index()])
            }
            Expr::Call(..) | Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) | Expr::Match(..) => {
                expr
            }
        }
    }

    /// The match on what dropping `position` left, as a match on whether
    /// the position is below the count: where it is, the element worked out
    /// at it where the match bound it, the rest it leaves unread after it,
    /// then the arm as it was.
    #[expect(
        clippy::too_many_lines,
        reason = "the arms rebuilt in one place, each constructor's in turn"
    )]
    fn found(&self, program: &mut Program, on: Atom, arms: super::Range, position: Atom) -> Expr {
        let TypeShape::Sequence {
            empty,
            push,
            recursive,
            ..
        } = type_shape(program, self.item)
        else {
            unreachable!("a reader reads a sequence");
        };
        let (_, yes, no) = self.less;
        let arms = program.arms(arms).to_vec();
        let body = |ctor| {
            arms.iter()
                .find(|arm| arm.ctor == ctor)
                .expect("an arm for each")
                .body
        };
        let (nil, cons) = (body(empty), body(push));
        let mut at_position = self.kept.clone();
        at_position.push(position);
        let worked = program.terms.hold_atoms(at_position.into_iter());
        let head = program.terms.push(Expr::Call(self.element.id, worked));
        let none = program.terms.hold_atoms(std::iter::empty());
        let rest = program.terms.push(Expr::Con(empty, none));
        let mut bindings = if recursive == 1 {
            vec![head, rest]
        } else {
            vec![rest, head]
        };
        bindings.extend_from_slice(program.bindings(cons.bindings));
        let found = program.terms.hold_body(&bindings, cons.tail);
        let mut arms = [
            Arm {
                ctor: yes,
                body: found,
            },
            Arm {
                ctor: no,
                body: nil,
            },
        ];
        arms.sort_by_key(|arm| program.tag(arm.ctor));
        Expr::Match(on, program.terms.hold_arms(&arms))
    }
}

/// `args` with what is at `at` replaced by `made`.
fn handed_for<T: Copy>(args: &[T], at: usize, made: &[T]) -> Vec<T> {
    let mut handed = Vec::with_capacity(args.len() + made.len());
    handed.extend_from_slice(&args[..at]);
    handed.extend_from_slice(made);
    handed.extend_from_slice(&args[at + 1..]);
    handed
}

/// The step of the walk `producer`, counting `nat` down: its arm for a
/// number one more than another.
fn step_of(program: &Program, producer: FnId, nat: super::TypeId) -> Body {
    let body = program.function(producer).body().expect("a producer");
    let (_, arms) = walk::top_match(program, body).expect("a producer's match");
    let TypeShape::Natural { empty, push, .. } = type_shape(program, nat) else {
        unreachable!("a producer counts a number");
    };
    let [_, step] = walk::split_arms(program, arms, empty, push).expect("a producer's arms");
    step.body
}

/// A call handing a reader a list a walk built, found in a body.
struct Site {
    call: ExprId,
    reader: FnId,
    list: usize,
    args: super::Range,
    producer: FnId,
    /// What the walk was handed, but the list it started from.
    made: Vec<Atom>,
}

struct Indexed<'a> {
    program: &'a mut Program,
    recognised: Recognised,
    /// Indexed by definition: see [`super::calls::pure`].
    pure: Vec<bool>,
    producers: HashMap<FnId, Option<Producer>>,
    readers: HashMap<(FnId, usize), Option<Reader>>,
    elements: HashMap<FnId, Element>,
    copies: HashMap<(FnId, usize, FnId), FnId>,
}

impl Indexed<'_> {
    /// Send each site in `id`'s body to its reader's copy, answering
    /// whether there was one.
    fn rewrite(&mut self, id: FnId) -> bool {
        if self.recognised.answered(id) {
            return false;
        }
        let Some(body) = self.program.function(id).body() else {
            return false;
        };
        let mut sites = Vec::new();
        self.sites(body, self.program.params(id).len(), &mut sites);
        let mut rewrote = false;
        for site in sites {
            let Some(copy) = self.copy(&site) else {
                continue;
            };
            let args = self.program.atoms(site.args).to_vec();
            let handed = handed_for(&args, site.list, &site.made);
            let handed = self.program.terms.hold_atoms(handed.into_iter());
            self.program.write(site.call, Expr::Call(copy, handed));
            rewrote = true;
        }
        rewrote
    }

    /// Each call in `body`, whose first binding takes `base`, handing a
    /// reader a list built by a counting walk from nothing and read by
    /// nothing else; and the same in every arm.
    fn sites(&mut self, body: Body, base: usize, sites: &mut Vec<Site>) {
        let bindings = self.program.bindings(body.bindings).to_vec();
        for (at, &expr) in bindings.iter().enumerate() {
            let level = base + at;
            if let Some(site) = self.site(body, base, level, expr) {
                sites.push(site);
            }
        }
        // Arms bind their fields from the level of the binding they are in.
        for (at, &expr) in bindings.iter().chain([&body.tail]).enumerate() {
            if let Expr::Match(_, arms) = self.program.expr(expr) {
                for arm in self.program.arms(arms).to_vec() {
                    let fields = self.program.fields(arm.ctor).len();
                    self.sites(arm.body, base + at + fields, sites);
                }
            }
        }
    }

    /// The site where `expr`, binding `level` of `body`, builds a list a
    /// reader reads and nothing else does.
    #[expect(
        clippy::too_many_lines,
        reason = "each condition of the site is one early return, read in order"
    )]
    fn site(&mut self, body: Body, base: usize, level: usize, expr: ExprId) -> Option<Site> {
        let Expr::Call(producer, made) = self.program.expr(expr) else {
            return None;
        };
        let shape = self.producer(producer)?;
        let made = self.program.atoms(made).to_vec();
        // Built from nothing: the list it starts from is the empty one.
        if !self.empty(producer, shape.acc, body, base, made[shape.acc]) {
            return None;
        }
        // Read once after it is made, by a call handing it on once.
        let later = &self.program.bindings(body.bindings)[level + 1 - base..];
        let exprs: Vec<ExprId> =
            walk::nested(self.program, later.iter().copied().chain([body.tail])).collect();
        if walk::reads(self.program, exprs.iter().copied(), level) != 1 {
            return None;
        }
        let (call, reader, args) =
            exprs
                .iter()
                .find_map(|&expr| match self.program.expr(expr) {
                    Expr::Call(callee, args)
                        if self.program.atoms(args).contains(&Atom(Local::at(level))) =>
                    {
                        Some((expr, callee, args))
                    }
                    _ => None,
                })?;
        let list = self
            .program
            .atoms(args)
            .iter()
            .position(|atom| atom.0.index() == level)?;
        self.reader(reader, list)?;
        let made = made
            .iter()
            .enumerate()
            .filter(|&(at, _)| at != shape.acc)
            .map(|(_, &atom)| atom)
            .collect();
        Some(Site {
            call,
            reader,
            list,
            args,
            producer,
            made,
        })
    }

    /// Whether `atom`, in `body` whose first binding takes `base`, is the
    /// empty list `producer` takes at `acc`.
    fn empty(&self, producer: FnId, acc: usize, body: Body, base: usize, atom: Atom) -> bool {
        let Some(start) = walk::bound(self.program, body, base, atom.0.index()) else {
            return false;
        };
        let acc_type = self.program.params(producer)[acc];
        let TypeShape::Sequence { empty, .. } = type_shape(self.program, acc_type) else {
            return false;
        };
        match self.program.expr(start) {
            Expr::Static(value) => self.program.constant(value).constructor() == empty,
            Expr::Con(ctor, _) => ctor == empty,
            Expr::Atom(_) | Expr::Call(..) | Expr::Match(..) => false,
        }
    }

    /// Whether `id` builds a list a position at a time:
    ///
    /// ```text
    /// p(.. count .. acc ..) = match count
    ///   zero => acc
    ///   succ(rest) => ...; e = ...; next = append(acc, e); p(.. rest .. next ..)
    /// ```
    ///
    /// handing every other parameter on as it came or one more, reading
    /// `acc` only to append to it and `rest` only to go on, and reaching no
    /// bodyless call.
    fn producer(&mut self, id: FnId) -> Option<Producer> {
        if let Some(known) = self.producers.get(&id) {
            return known.clone();
        }
        let found = self.find_producer(id);
        self.producers.insert(id, found.clone());
        found
    }

    fn find_producer(&self, id: FnId) -> Option<Producer> {
        if self.recognised.answered(id) || !self.pure.get(id.index()).copied().unwrap_or(false) {
            return None;
        }
        let program = &*self.program;
        let body = program.function(id).body()?;
        let params = program.params(id);
        let arity = params.len();
        let (count, arms) = walk::top_match(program, body)?;
        let TypeShape::Natural { empty, push, .. } = type_shape(program, params[count]) else {
            return None;
        };
        let [zero, step] = walk::split_arms(program, arms, empty, push)?;
        let Expr::Atom(Atom(acc)) = program.expr(zero.body.tail) else {
            return None;
        };
        let acc = acc.index();
        if acc >= arity || acc == count {
            return None;
        }
        let up = self.stepped(id, step.body, count, acc)?;
        // The list only appended to, the rest only gone on with, and the
        // count read only by the match.
        let reads = |level| walk::reads(program, walk::within(program, step.body), level);
        (reads(acc) == 1 && reads(arity) == 1 && reads(count) == 0).then_some(Producer {
            count,
            acc,
            up,
        })
    }

    /// Which of `id`'s parameters its step, `body`, counts up by one, where
    /// it appends one element to `acc`, goes on with the rest of `count`,
    /// and hands every other parameter on as it came or one more.
    fn stepped(&self, id: FnId, body: Body, count: usize, acc: usize) -> Option<Vec<bool>> {
        let program = &*self.program;
        let arity = program.params(id).len();
        let base = arity + 1;
        let Expr::Call(again, args) = program.expr(body.tail) else {
            return None;
        };
        let args = program.atoms(args);
        if again != id || args[count] != Atom(Local::at(arity)) {
            return None;
        }
        let appended = walk::bound(program, body, base, args[acc].0.index())?;
        let Expr::Call(append, onto) = program.expr(appended) else {
            return None;
        };
        if self.recognised.sequences.get(append.index()) != Some(&Some(SequenceOperation::Append))
            || program.atoms(onto)[0] != Atom(Local::at(acc))
        {
            return None;
        }
        let mut up = vec![false; arity];
        for (at, &arg) in args.iter().enumerate() {
            if at == count || at == acc || arg == Atom(Local::at(at)) {
                continue;
            }
            if !self.one_more(body, base, arg, at) {
                return None;
            }
            up[at] = true;
        }
        Some(up)
    }

    /// Whether `arg`, in `body` whose first binding takes `base`, is
    /// parameter `at` plus one.
    fn one_more(&self, body: Body, base: usize, arg: Atom, at: usize) -> bool {
        let Some(bound) = walk::bound(self.program, body, base, arg.0.index()) else {
            return false;
        };
        let Expr::Call(add, operands) = self.program.expr(bound) else {
            return false;
        };
        if self.recognised.operations.get(add.index()) != Some(&Some(Operation::Add)) {
            return false;
        }
        let one = |atom: Atom| {
            walk::bound(self.program, body, base, atom.0.index())
                .is_some_and(|expr| self.is_one(expr))
        };
        match *self.program.atoms(operands) {
            [a, b] => (a == Atom(Local::at(at)) && one(b)) || (b == Atom(Local::at(at)) && one(a)),
            _ => false,
        }
    }

    /// Whether `expr` is the natural one.
    fn is_one(&self, expr: ExprId) -> bool {
        let Expr::Static(value) = self.program.expr(expr) else {
            return false;
        };
        matches!(self.program.constant(value).view(),
            ConstantView::Natural(natural) if natural.try_u64() == Ok(1))
    }

    /// Whether `id` reads its parameter `list` only by its length, by what
    /// dropping a position leaves, taken apart at once, and by handing it
    /// on to itself; reading one position at most, which it counts up each
    /// time it goes round.
    fn reader(&mut self, id: FnId, list: usize) -> Option<Reader> {
        if let Some(&known) = self.readers.get(&(id, list)) {
            return known;
        }
        let found = self.find_reader(id, list);
        self.readers.insert((id, list), found);
        found
    }

    #[expect(
        clippy::too_many_lines,
        reason = "each condition of the reader is one early return, read in order"
    )]
    fn find_reader(&self, id: FnId, list: usize) -> Option<Reader> {
        if self.recognised.answered(id) {
            return None;
        }
        let program = &*self.program;
        let body = program.function(id).body()?;
        let arity = program.params(id).len();
        let TypeShape::Sequence {
            empty,
            push,
            recursive,
            ..
        } = type_shape(program, program.params(id)[list])
        else {
            return None;
        };
        let (reader, drops, goes_on) = self.list_reads(id, body, list)?;
        // Every call of itself hands the list on where it took it.
        let handed_on = walk::within(program, body).all(|expr| match program.expr(expr) {
            Expr::Call(callee, args) if callee == id => {
                program.atoms(args)[list] == Atom(Local::at(list))
            }
            _ => true,
        });
        if !handed_on || drops.len() > 1 {
            return None;
        }
        // What dropping leaves is taken apart at once, its rest unread.
        if let Some(&(level, _)) = drops.first()
            && !self.taken_apart(body, arity, level, (empty, push, recursive))
        {
            return None;
        }
        // Going round, the position read is one it counts up.
        if goes_on && let Some(&(_, position)) = drops.first() {
            let at = position.0.index();
            if at >= arity {
                return None;
            }
            let calls = self_calls(program, &self.recognised, id, body);
            if !calls.iter().all(|call| call[at] == Handed::Step(at)) {
                return None;
            }
        }
        Some(reader)
    }

    /// What reads `id`'s parameter `list` in `body`, where nothing but its
    /// length, dropping a position of it and handing it on to itself does:
    /// which length and drop it calls, each position dropped with the
    /// level its answer takes, and whether it goes round.
    #[expect(
        clippy::too_many_lines,
        reason = "one walk over the body, a case for each way of reading the list"
    )]
    fn list_reads(&self, id: FnId, body: Body, list: usize) -> Option<ListReads> {
        let program = &*self.program;
        let operation = |callee: FnId| {
            self.recognised
                .sequences
                .get(callee.index())
                .copied()
                .flatten()
        };
        let (mut length, mut drop) = (None, None);
        let mut drops = Vec::new();
        let mut goes_on = false;
        let mut ok = true;
        let arity = program.params(id).len();
        scoped(program, body, &mut vec![None; arity], &mut |expr, bound| {
            if !walk::operands(program, expr).any(|atom| atom.0.index() == list) {
                return;
            }
            match program.expr(expr) {
                Expr::Call(callee, args) if callee == id => {
                    let args = program.atoms(args);
                    ok &= args.iter().filter(|atom| atom.0.index() == list).count() == 1;
                    goes_on = true;
                }
                Expr::Call(callee, args)
                    if operation(callee) == Some(SequenceOperation::Length) =>
                {
                    ok &= length.is_none_or(|known| known == callee)
                        && program.atoms(args).len() == 1;
                    length = Some(callee);
                }
                Expr::Call(callee, args) if operation(callee) == Some(SequenceOperation::Drop) => {
                    let args = program.atoms(args);
                    ok &= drop.is_none_or(|known| known == callee)
                        && args[0].0.index() == list
                        && args[1].0.index() != list;
                    drop = Some(callee);
                    drops.push((bound.len(), args[1]));
                }
                _ => ok = false,
            }
        });
        ok.then_some((Reader { length, drop }, drops, goes_on))
    }

    /// Whether the binding at `level` of `id`'s body, which drops a
    /// position, is read only by one match taking it apart, whose rest it
    /// leaves unread.
    fn taken_apart(
        &self,
        body: Body,
        arity: usize,
        level: usize,
        (empty, push, recursive): (CtorId, CtorId, usize),
    ) -> bool {
        let program = &*self.program;
        let (mut matches, mut others, mut rest_read) = (0, 0, false);
        scoped(program, body, &mut vec![None; arity], &mut |expr, bound| {
            let reads = walk::operands(program, expr)
                .filter(|atom| atom.0.index() == level)
                .count();
            if reads == 0 {
                return;
            }
            match program.expr(expr) {
                Expr::Match(on, arms) if on.0.index() == level => {
                    let Some([_, cons]) = walk::split_arms(program, arms, empty, push) else {
                        others += 1;
                        return;
                    };
                    // The arm binds its fields from the level the match
                    // takes: the rest is the recursive one.
                    let rest = bound.len() + recursive;
                    rest_read |= walk::reads(program, walk::within(program, cons.body), rest) > 0;
                    matches += 1;
                }
                _ => others += reads,
            }
        });
        matches == 1 && others == 0 && !rest_read
    }

    /// The definition working out the element at a position of what
    /// `producer` builds, made the first time it is asked for: its step,
    /// with each number it counts up moved on by the position, answering
    /// what it appends.
    #[expect(
        clippy::too_many_lines,
        reason = "the definition declared and its body written in one place"
    )]
    fn element(&mut self, producer: FnId) -> Element {
        if let Some(&known) = self.elements.get(&producer) {
            return known;
        }
        let shape = self.producer(producer).expect("a producer");
        let add = self.add();
        let program = &mut *self.program;
        let params = program.params(producer).to_vec();
        let nat = params[shape.count];
        let kept: Vec<usize> = (0..params.len())
            .filter(|&at| at != shape.count && at != shape.acc)
            .collect();
        let mut types: Vec<_> = kept.iter().map(|&at| params[at]).collect();
        types.push(nat);
        let TypeShape::Sequence { element, .. } =
            type_shape(program, program.function(producer).result)
        else {
            unreachable!("a producer builds a sequence");
        };
        let name = format!("{}.at", program.name(program.function(producer).name));
        let id = program.declare(&name, &types, element);
        let step = step_of(program, producer, nat);
        let position = Atom(Local::at(kept.len()));
        let mut scope = Scope::at(kept.len() + 1);
        let mut locals = vec![UNREAD; params.len() + 1];
        for (place, &at) in kept.iter().enumerate() {
            let held = Atom(Local::at(place));
            locals[at] = if shape.up[at] {
                let add = add
                    .filter(|&add| program.params(add) == [params[at], nat])
                    .expect("a step is a recognized sum");
                let operands = program.terms.hold_atoms([held, position].into_iter());
                copy::push(program, &mut scope, Expr::Call(add, operands))
            } else {
                held
            };
        }
        // What the step appends, and going on, become that element.
        let mut pushed = None;
        let mut edit = |program: &mut Program, scope: &mut Scope, _: ExprId, expr: Expr| match expr
        {
            Expr::Call(callee, _) if callee == producer => {
                Expr::Atom(pushed.expect("the element appended before going on"))
            }
            Expr::Call(_, args) if program.atoms(args).first() == Some(&UNREAD) => {
                pushed = Some(Atom(Local::at(scope.level)));
                Expr::Atom(program.atoms(args)[1])
            }
            Expr::Call(..) | Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) | Expr::Match(..) => {
                expr
            }
        };
        let answer = copy::into(program, step, locals, &mut scope, Some(&mut edit));
        let body = copy::close(program, scope, answer);
        program.replace_bodies(vec![(id, body)]);
        let made = Element { id };
        self.elements.insert(producer, made);
        made
    }

    /// The definition recognized as a sum, where there is one.
    fn add(&self) -> Option<FnId> {
        self.recognised
            .operations
            .iter()
            .position(|operation| *operation == Some(Operation::Add))
            .map(FnId::at)
    }

    /// The copy of the site's reader taking what its walk was handed in
    /// its list's place, made the first time it is asked for.
    #[expect(
        clippy::too_many_lines,
        reason = "the copy declared and its body written in one place"
    )]
    fn copy(&mut self, site: &Site) -> Option<FnId> {
        let key = (site.reader, site.list, site.producer);
        if let Some(&known) = self.copies.get(&key) {
            return Some(known);
        }
        let reader = self.reader(site.reader, site.list)?;
        let shape = self.producer(site.producer)?;
        let less = self.less_than(self.program.params(site.producer)[shape.count])?;
        let element = self.element(site.producer);
        let program = &mut *self.program;
        let made_types: Vec<_> = program
            .params(site.producer)
            .iter()
            .enumerate()
            .filter(|&(at, _)| at != shape.acc)
            .map(|(_, &ty)| ty)
            .collect();
        let originals = program.params(site.reader).to_vec();
        let item = originals[site.list];
        let types = handed_for(&originals, site.list, &made_types);
        let name = format!(
            "{}.{}",
            program.name(program.function(site.reader).name),
            program.functions().len()
        );
        let id = program.declare(&name, &types, program.function(site.reader).result);
        self.copies.insert(key, id);
        // The reader's parameters, its list standing for nothing it may
        // read, and what the walk was handed in its place.
        let all: Vec<Atom> = (0..types.len()).map(|at| Atom(Local::at(at))).collect();
        let made = all[site.list..site.list + made_types.len()].to_vec();
        let mut locals = all[..site.list].to_vec();
        locals.push(UNREAD);
        locals.extend_from_slice(&all[site.list + made_types.len()..]);
        // The count among what the walk was handed, and the rest, which
        // the element is worked out of.
        let count_at = shape.count - usize::from(shape.acc < shape.count);
        let read = Read {
            copy: id,
            count: made[count_at],
            kept: made
                .iter()
                .enumerate()
                .filter(|&(at, _)| at != count_at)
                .map(|(_, &atom)| atom)
                .collect(),
            made,
            element,
            less,
            item,
        };
        let mut dropped: HashMap<usize, Atom> = HashMap::default();
        let mut edit = |program: &mut Program, scope: &mut Scope, _: ExprId, expr: Expr| {
            read.rewritten(program, (site.reader, reader), &mut dropped, scope, expr)
        };
        let body = program.function(site.reader).body().expect("a reader");
        let copied = copy::body(program, body, locals, types.len(), Some(&mut edit));
        program.replace_bodies(vec![(id, copied)]);
        Some(id)
    }

    /// The definition recognized as less-than over two numbers of `ty`, and
    /// its two answers.
    fn less_than(&self, ty: super::TypeId) -> Option<(FnId, CtorId, CtorId)> {
        (0..self.program.functions().len())
            .map(FnId::at)
            .find_map(|id| {
                let Some(Some(Operation::LessThan { yes, no })) =
                    self.recognised.operations.get(id.index())
                else {
                    return None;
                };
                (self.program.params(id) == [ty, ty]).then_some((id, *yes, *no))
            })
    }
}
