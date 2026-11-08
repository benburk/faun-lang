//! What a number can be, worked out from what a program does with it.
//!
//! A type says a value is a number and nothing about which numbers, so
//! deciding how wide to hold one is deciding what it could be. That is a
//! question about terms, not about storage: `Succ` is one more than what it
//! wraps, a match on `Zero` says which argument is nought in which arm, and
//! a call answers whatever the name it calls does. None of it needs a word
//! size, which is why it is worked out here and read below.
//!
//! What comes out is per term, since that is what the tier deciding
//! representation walks: every term has an answer, so how wide to hold what
//! it answers is a question with one. A term walked more than once -- an
//! arm reached at two widths, a definition gone round again -- holds what
//! it held at any of them.
//!
//! A field is held the same way: every value built into one field of one
//! constructor, anywhere, is what reading that field back can answer. That
//! is what lets a number inside a product be held as narrowly as a number
//! outside one. A value no walk sees built -- handed in at the entry, or
//! answered by something outside -- could hold anything in any field it
//! reaches.
//!
//! Nothing here is exact. A bound too wide costs a wider number and never a
//! wrong one, so where the walk cannot say -- a definition that counts up
//! without a last step, an argument from outside -- it says so and the
//! tiers below hold what they must.

use super::counters::Counter;
use super::facts::{Recognised, SequenceOperation};
use super::model::{Body, CtorId, Expr, ExprId, FnId, Range, TypeId};
use super::program::Program;
use super::{Shape, shape, single_field};
pub use crate::facts::Facts as Bounds;

/// Whether a value these bounds hold could be built with this constructor.
/// Nought is not a `Succ` of anything and nothing above nought is `Zero`,
/// and a tag is the one number it is.
fn reaches(program: &Program, held: Bounds, spine: Shape, ctor: CtorId) -> bool {
    if single_field(program, program.ctor(ctor).owner).is_some() {
        return true;
    }
    match spine {
        Shape::Spine { nil, .. } if ctor == nil => held.low == 0,
        Shape::Spine { .. } => held.high != Some(0),
        Shape::Tagged => {
            let tag = u64::from(program.tag(ctor));
            held.low <= tag && held.high.is_none_or(|high| tag <= high)
        }
    }
}

/// How many times the walk goes round before it stops trying to be exact.
/// A definition that counts up without a last step grows every round, and
/// past this a growing bound is answered with no bound at all.
const WIDEN: usize = 8;

/// And how many times it goes round at all, beyond one for each definition.
/// Past widening a bound only ever settles, but what a definition learns
/// reaches a caller walked before it only on the next round, so a chain of
/// calls takes a round for each link: the room that takes grows with the
/// program, and this is what is left over for settling.
const ROUNDS: usize = 32;

/// How many times the walk goes round afterwards to take back what widening
/// gave up. Each round carries a narrower bound one call further.
const NARROWINGS: usize = 8;

/// Final conservative ranges consumed by lowering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Ranges {
    /// What each term answers, by the term.
    pub terms: Vec<Bounds>,
    pub matched: Vec<Bounds>,
    /// What each definition is handed, by definition.
    pub takes: Vec<Vec<Bounds>>,
    /// And what each answers.
    pub answers: Vec<Bounds>,
    /// What each constructor field holds, by its place in the field pool.
    pub fields: Vec<Bounds>,
}

pub(super) fn analyze(program: &Program, recognised: &Recognised, assumed: &Assumed) -> Ranges {
    let count = program.functions().len();
    let counters = super::counters::counters(program, &recognised.operations);
    let mut held = Propagation::start(program, assumed, &counters);

    let mut settled = false;
    for round in 0..ROUNDS + count {
        let mut again = false;
        for at in 0..count {
            again |= once(
                program,
                recognised,
                assumed,
                &mut held,
                (FnId::at(at), round),
            );
        }
        if !again {
            settled = true;
            break;
        }
    }

    // A bound still on its way up is a bound too small, and a bound too
    // small is the one mistake this must not make: it would hold a value in
    // fewer bits than the value has. Widening settles what recursion leaves
    // growing, so reaching here means something grew in a way widening does
    // not reach -- and then nothing here is known.
    if !settled {
        held.forget();
    }

    // Widening gives up more than recursion needs it to: a remainder of a
    // count that grew is still below its divisor, and what is handed that
    // remainder is too. Going round again from a bound that holds, without
    // widening, only takes away what nothing reaches.
    for _ in 0..NARROWINGS {
        let next = narrowed(program, recognised, assumed, &held);
        if next == held {
            break;
        }
        held = next;
    }

    finish(program, assumed, held)
}

/// What the tier lowering a program assumes of values that come from
/// outside it: what its routines answer and what its target hands the entry.
///
/// Barb works out what the program itself says and nothing about any
/// target; these are asked of an analysis by the tier that knows the target,
/// and what comes out belongs to that tier, never to the program.
#[derive(Clone, Debug, Default)]
pub struct Assumed {
    /// What a declaration with no body answers.
    pub results: Vec<(FnId, Bounds)>,
    /// What the entry's parameters are handed, by place.
    pub parameters: Vec<(usize, Bounds)>,
    /// What every value of a constructor holds in one field.
    pub fields: Vec<(CtorId, usize, Bounds)>,
    /// What any sequence's length can be, where anything says.
    pub length: Option<Bounds>,
    /// Whether a claimed float is answered by a machine rather than by its
    /// body; where it is not, the claim is no fact of the program's.
    pub floats: bool,
}

impl Assumed {
    fn result(&self, id: FnId) -> Bounds {
        self.results
            .iter()
            .find(|(of, _)| *of == id)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    fn parameter(&self, at: usize) -> Bounds {
        self.parameters
            .iter()
            .find(|(of, _)| *of == at)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    fn field(&self, ctor: CtorId, at: usize) -> Bounds {
        self.fields
            .iter()
            .find(|(of, place, _)| *of == ctor && *place == at)
            .map_or(Bounds::ANY, |(_, _, bounds)| *bounds)
    }

    /// What a value of `ty` built outside is: anything, but for what is
    /// assumed of the one field of each wrapper it is held through. A wrapper
    /// is its field, so that bounds the value itself.
    fn value(&self, program: &Program, ty: TypeId) -> Bounds {
        let mut held = Bounds::ANY;
        let mut ty = ty;
        for _ in 0..program.types().len() {
            let Some((ctor, field)) = single_field(program, ty) else {
                break;
            };
            held = held.and(self.field(ctor, 0));
            ty = field;
        }
        held
    }
}

/// How many field places the program declares, end to end.
fn field_slots(program: &Program) -> usize {
    (0..program.types().len())
        .flat_map(|ty| program.ctors(TypeId::at(ty)))
        .map(|ctor| ctor.fields.range().end)
        .max()
        .unwrap_or(0)
}

/// The place one field of one constructor has in the field pool.
pub(super) fn slot(program: &Program, ctor: CtorId, at: usize) -> usize {
    program.ctor(ctor).fields.range().start + at
}

/// Say that every field reachable from `roots` could hold anything but what
/// is assumed of it: values of those types were built where nothing here
/// walks.
fn unknown(program: &Program, assumed: &Assumed, roots: &[TypeId], fields: &mut [Option<Bounds>]) {
    let mut seen = vec![false; program.types().len()];
    let mut waiting = roots.to_vec();
    while let Some(ty) = waiting.pop() {
        if std::mem::replace(&mut seen[ty.index()], true) {
            continue;
        }
        for (tag, ctor) in program.ctors(ty).iter().enumerate() {
            let id = program.ctor_at(ty, u32::try_from(tag).expect("a sane constructor count"));
            for (at, place) in fields[ctor.fields.range()].iter_mut().enumerate() {
                *place = Some(assumed.field(id, at));
            }
            waiting.extend_from_slice(program.types_of(ctor.fields));
        }
    }
}

/// What the walk worked out, as the tier below reads it.
fn finish(program: &Program, assumed: &Assumed, held: Propagation) -> Ranges {
    // A spine's rest is read as a step of its count, not as what was built
    // there, so nothing is said of that field.
    let takes = held
        .params
        .iter()
        .enumerate()
        .map(|(at, params)| {
            let mut takes: Vec<_> = params.iter().copied().map(anything).collect();
            held.counted(FnId::at(at), &mut takes);
            takes
        })
        .collect();
    let mut fields: Vec<_> = held.fields.into_iter().map(anything).collect();
    for ty in 0..program.types().len() {
        if let Shape::Spine {
            cons, recursive, ..
        } = shape(program, TypeId::at(ty))
        {
            fields[slot(program, cons, recursive)] = Bounds::ANY;
        }
    }
    // What is assumed of a field holds wherever the value was built.
    for &(ctor, at, bounds) in &assumed.fields {
        let place = slot(program, ctor, at);
        fields[place] = fields[place].and(bounds);
    }
    // A term nothing reached is a term nothing knows, and so is a parameter
    // nothing was ever handed.
    Ranges {
        matched: held
            .matched
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
        terms: held
            .terms
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
        takes,
        answers: held.results.into_iter().map(anything).collect(),
        fields,
    }
}

/// What nothing known comes out as. The walk starts at nothing so that one
/// name's ignorance does not spread to every name that calls it; what comes
/// out is read by a tier that has to hold something, and nothing known
/// there means anything at all.
const fn anything(held: Option<Bounds>) -> Bounds {
    match held {
        Some(held) if !held.is_nothing() => held,
        _ => Bounds::ANY,
    }
}

/// What the walk has worked out so far, which is what it goes round again
/// to add to.
#[derive(PartialEq, Eq)]
struct Propagation {
    params: Vec<Vec<Option<Bounds>>>,
    /// Each definition's counters, and the most each count and what it
    /// walks sum to where they come in from outside: see [`counters`].
    counters: Vec<Vec<(Counter, Sum)>>,
    results: Vec<Option<Bounds>>,
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    /// What each field was built with, by its place in the field pool.
    fields: Vec<Option<Bounds>>,
}

/// What each definition is handed before anything is walked: what the tier
/// above assumes of the entry's parameters, and nothing of anyone else's.
fn handed(program: &Program, assumed: &Assumed) -> Vec<Vec<Option<Bounds>>> {
    let (count, entry) = (program.functions().len(), program.entry());
    (0..count)
        .map(|at| {
            let id = FnId::at(at);
            if entry == Some(id) {
                program
                    .params(id)
                    .iter()
                    .enumerate()
                    .map(|(at, &ty)| Some(assumed.parameter(at).and(assumed.value(program, ty))))
                    .collect()
            } else {
                vec![None; program.params(id).len()]
            }
        })
        .collect()
}

impl Propagation {
    /// Where the walk starts: nothing known of anything reached from inside,
    /// and anything at all in the fields of what comes in from outside.
    fn start(program: &Program, assumed: &Assumed, counters: &[Vec<Counter>]) -> Self {
        let count = program.functions().len();
        let entry = program.entry();
        // A parameter nothing has handed anything to yet is a parameter nothing
        // is known of, which is not the same as one anything could be handed.
        let mut held = Self {
            params: handed(program, assumed),
            counters: counters
                .iter()
                .map(|found| {
                    found
                        .iter()
                        .map(|&counter| (counter, Sum::Unseen))
                        .collect()
                })
                .collect(),
            results: vec![None; count],
            terms: vec![Bounds::NOTHING; program.exprs_count()],
            matched: vec![Bounds::NOTHING; program.exprs_count()],
            fields: vec![None; field_slots(program)],
        };
        // What comes in from outside was built where no walk sees it.
        let mut outside: Vec<TypeId> = Vec::new();
        for (at, function) in program.functions().iter().enumerate() {
            if entry == Some(FnId::at(at)) {
                outside.extend_from_slice(program.params(FnId::at(at)));
            }
            if function.body().is_none() {
                outside.push(function.result);
            }
        }
        unknown(program, assumed, &outside, &mut held.fields);
        held
    }

    /// Say nothing is known, which is what a walk that did not settle knows.
    fn forget(&mut self) {
        self.terms.fill(Bounds::ANY);
        self.matched.fill(Bounds::ANY);
        self.params.iter_mut().flatten().for_each(|held| {
            *held = Some(Bounds::ANY);
        });
        self.results.fill(Some(Bounds::ANY));
        self.fields.fill(Some(Bounds::ANY));
    }

    /// Take in what one walk found it built and called, answering whether
    /// any of it was more than was known.
    fn learn(
        &mut self,
        program: &Program,
        assumed: &Assumed,
        (found, caller): (Found, FnId),
        round: usize,
    ) -> bool {
        let mut again = false;
        for (place, bounds) in found.built {
            again |= settle(&mut self.fields[place], bounds, round);
        }
        if !found.outside.is_empty() {
            let before = self.fields.clone();
            unknown(program, assumed, &found.outside, &mut self.fields);
            again |= self.fields != before;
        }
        for (called, args) in found.calls {
            if called != caller {
                again |= self.summed(called, &args);
            }
            for (at, bounds) in args.into_iter().enumerate() {
                again |= settle(&mut self.params[called.index()][at], bounds, round);
            }
        }
        again
    }
}

/// The most a count and what it walks sum to where calls from outside hand
/// them in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sum {
    /// No call from outside has been seen.
    Unseen,
    Most(u64),
    /// Some call hands one of them no greatest.
    Unbounded,
}

impl Propagation {
    /// Take in the sum a call from outside hands each of `called`'s
    /// counters and what it walks, answering whether any grew.
    fn summed(&mut self, called: FnId, args: &[Bounds]) -> bool {
        let mut again = false;
        for (counter, most) in &mut self.counters[called.index()] {
            let sum = args[counter.counter]
                .high
                .zip(args[counter.measure].high)
                .and_then(|(count, walked)| count.checked_add(walked));
            let joined = match (*most, sum) {
                (Sum::Unseen, Some(sum)) => Sum::Most(sum),
                (Sum::Most(before), Some(sum)) => Sum::Most(before.max(sum)),
                _ => Sum::Unbounded,
            };
            again |= joined != *most;
            *most = joined;
        }
        again
    }

    /// What `id`'s parameters are, each count no more than what it and
    /// what it walks sum to where they come in.
    fn counted(&self, id: FnId, params: &mut [Bounds]) {
        for &(counter, most) in &self.counters[id.index()] {
            if let Sum::Most(most) = most {
                params[counter.counter] = params[counter.counter].and(Bounds {
                    low: 0,
                    high: Some(most),
                });
            }
        }
    }
}

/// How a matched constructor's fields are bound: all alike, or each as what
/// was built into it, but for a spine's rest, which is its count less one.
#[derive(Clone, Copy)]
enum Binding {
    Whole(Bounds),
    Built(Option<(usize, Bounds)>),
}

/// What one walk hands on: the arguments it called with, what it built into
/// each field, and the types of values it met built out of sight.
#[derive(Default)]
struct Found {
    calls: Vec<(FnId, Vec<Bounds>)>,
    built: Vec<(usize, Bounds)>,
    outside: Vec<TypeId>,
}

/// One definition, once. Answers whether anything it worked out was more
/// than what was already known, which is what says to go round again.
fn once(
    program: &Program,
    recognised: &Recognised,
    assumed: &Assumed,
    held: &mut Propagation,
    (id, round): (FnId, usize),
) -> bool {
    // Results change only after this walk; borrowing retains the same
    // per-function snapshot without copying the whole table each round.
    let (mut terms, mut matched) = (
        std::mem::take(&mut held.terms),
        std::mem::take(&mut held.matched),
    );
    let walked = walk(
        (program, recognised, assumed),
        held,
        id,
        (&mut terms, &mut matched),
    );
    held.terms = terms;
    held.matched = matched;
    let Some((answer, found)) = walked else {
        return false;
    };
    let again = settle(&mut held.results[id.index()], answer, round);
    held.learn(program, assumed, (found, id), round) || again
}

/// Every definition once more, reading only what `held` knows and building
/// what that says afresh. Where `held` already holds everything its walks
/// find, so does the answer, and it holds no more: a bound widened past
/// what the program reaches comes back down.
fn narrowed(
    program: &Program,
    recognised: &Recognised,
    assumed: &Assumed,
    held: &Propagation,
) -> Propagation {
    let counters: Vec<Vec<Counter>> = held
        .counters
        .iter()
        .map(|found| found.iter().map(|&(counter, _)| counter).collect())
        .collect();
    let mut next = Propagation::start(program, assumed, &counters);
    for at in 0..program.functions().len() {
        let Some((answer, found)) = walk(
            (program, recognised, assumed),
            held,
            FnId::at(at),
            (&mut next.terms, &mut next.matched),
        ) else {
            continue;
        };
        next.results[at] = Some(answer);
        next.learn(program, assumed, (found, FnId::at(at)), 0);
    }
    next
}

/// What one definition answers and hands on, given what `held` knows, with
/// what each of its terms answers joined into `terms` and `matched`. Nothing,
/// while nothing has handed it anything.
fn walk(
    (program, recognised, assumed): (&Program, &Recognised, &Assumed),
    held: &Propagation,
    id: FnId,
    (terms, matched): (&mut [Bounds], &mut [Bounds]),
) -> Option<(Bounds, Found)> {
    let mut params: Vec<Bounds> = held.params[id.index()]
        .iter()
        .copied()
        .collect::<Option<_>>()?;
    held.counted(id, &mut params);
    let Some(body) = program.function(id).body() else {
        // Something outside answers, and nothing about a declaration can be
        // read, so what comes back from one is what the tier above said.
        let result = program.function(id).result;
        let answered = assumed.result(id).and(assumed.value(program, result));
        return Some((answered, Found::default()));
    };

    // A recognized equation is evaluated as that operation, not walked as
    // unary recursion. Besides being cheaper, this avoids widening a huge
    // countdown one predecessor at a time.
    if let Some(op) = recognised.operations[id.index()] {
        let answer = operation(program, op, params[0], params[1]);
        return Some((answer, Found::default()));
    }
    // A sequence holds its length, so a count of one reads it; what it can
    // be is what the tier holding sequences says.
    if recognised.sequences[id.index()] == Some(SequenceOperation::Length) {
        return Some((assumed.length.unwrap_or(Bounds::ANY), Found::default()));
    }

    let mut walk = FunctionWalk {
        program,
        assumed,
        operations: &recognised.operations,
        sequences: &recognised.sequences,
        results: &held.results,
        fields: &held.fields,
        built: Vec::new(),
        outside: Vec::new(),
        predicates: vec![None; params.len()],
        exact: vec![None; params.len()],
        scope: params,
        terms,
        matched,
        calls: Vec::new(),
    };
    let answer = walk.body(body);
    let found = Found {
        calls: walk.calls,
        built: walk.built,
        outside: walk.outside,
    };
    Some((answer, found))
}

/// Widen `held` by `found`, answering whether that changed it. Past the
/// rounds worth being exact for, a bound that grows is widened in the
/// direction it grew -- up to the next machine width, and past the widest
/// to no bound at all: a definition counting up without a last step, or
/// down from a large constant, would otherwise be walked once for every
/// number it can reach.
fn settle(held: &mut Option<Bounds>, found: Bounds, round: usize) -> bool {
    // Nothing yet, held or found, is no bound to have moved: the first
    // thing found is what is held, however late it is found.
    let before = match *held {
        Some(before) if !before.is_nothing() => before,
        _ => {
            let changed = *held != Some(found);
            *held = Some(found);
            return changed;
        }
    };
    if found.within(before) {
        return false;
    }
    let after = before.or(found);
    *held = Some(if round < WIDEN {
        after
    } else {
        // Past the rounds worth being exact for, a bound that moves is given
        // up in the direction it moved: a count going up has no greatest,
        // and one counting down from a large constant has nought as least.
        Bounds {
            low: if after.low < before.low {
                0
            } else {
                before.low
            },
            high: if after.high == before.high {
                before.high
            } else {
                after.high.and_then(threshold)
            },
        }
    });
    *held != Some(before)
}

/// Where a growing greatest is widened to: the next width a machine holds
/// a number in, and no bound past the widest. A value kept below one by a
/// remainder settles there rather than losing its bound -- and with it
/// every bound it is copied into, which narrowing cannot take back where a
/// field is copied into itself.
fn threshold(high: u64) -> Option<u64> {
    [
        u64::from(u8::MAX),
        u64::from(u16::MAX),
        u64::from(u32::MAX),
        u64::MAX,
    ]
    .into_iter()
    .find(|&width| width >= high)
}

/// The most elements of a constant sequence read one by one for what its
/// fields hold; past this, its fields could hold anything.
const ELEMENTS_READ: u64 = 4096;

/// One walk over one definition, with what it hands to what it calls.
struct FunctionWalk<'a> {
    program: &'a Program,
    assumed: &'a Assumed,
    operations: &'a [Option<super::Operation>],
    sequences: &'a [Option<SequenceOperation>],
    results: &'a [Option<Bounds>],
    /// What each field was built with so far, and what this walk builds.
    fields: &'a [Option<Bounds>],
    built: Vec<(usize, Bounds)>,
    /// Types of values this walk found built where it cannot see inside.
    outside: Vec<TypeId>,
    /// What each level holds here, which arms take back as they end.
    scope: Vec<Bounds>,
    predicates: Vec<Option<(super::Operation, usize, usize)>>,
    /// The natural each level is known to be outright, where it is one a
    /// bound cannot say exactly: past what a `u64` holds, `2^64` among
    /// them, which a remainder below it needs to be known as.
    exact: Vec<Option<u128>>,
    /// And what each term answers, joined over every walk of it.
    terms: &'a mut [Bounds],
    matched: &'a mut [Bounds],
    calls: Vec<(FnId, Vec<Bounds>)>,
}

impl FunctionWalk<'_> {
    fn body(&mut self, body: Body) -> Bounds {
        for &binding in self.program.bindings(body.bindings) {
            let held = self.expr(binding);
            if let Expr::Call(called, _) = self.program.expr(binding)
                && self
                    .program
                    .ctors(self.program.function(called).result)
                    .is_empty()
            {
                return Bounds::NOTHING;
            }
            let predicate = match self.program.expr(binding) {
                Expr::Call(called, args) => {
                    let op = self.operations[called.index()];
                    match op {
                        Some(
                            op @ (super::Operation::Equals { .. }
                            | super::Operation::LessThan { .. }),
                        ) => {
                            let args = self.program.atoms(args);
                            Some((op, args[0].0.index(), args[1].0.index()))
                        }
                        _ => None,
                    }
                }
                Expr::Atom(a) => self.predicates[a.0.index()],
                _ => None,
            };
            let exact = self.exact(binding);
            self.scope.push(held);
            self.predicates.push(predicate);
            self.exact.push(exact);
        }
        self.expr(body.tail)
    }

    /// What a call answers, beyond what its equations or its body say: a
    /// remainder is below its divisor, even one past what a bound can say
    /// exactly, so `n % 2^64` is a number a word holds; and a claimed float
    /// may be answered by a machine rather than its body, whose NaN need not
    /// be the body's -- any pattern of the format, built into each wrapper
    /// out of sight.
    fn claimed(&mut self, called: FnId, args: Range, mut answer: Bounds) -> Bounds {
        if self.operations.get(called.index()).copied().flatten() == Some(super::Operation::Mod)
            && let Some(divisor) = self.exact[self.program.atoms(args)[1].0.index()]
            && let Ok(greatest) = u64::try_from(divisor.saturating_sub(1))
            && divisor > 0
        {
            answer = answer.and(Bounds {
                low: 0,
                high: Some(greatest),
            });
        }
        let function = self.program.function(called);
        if let Some(float) = function.float
            && let Some((wrappers, _)) = super::claim::wrapped(self.program, function.result)
        {
            let pattern = Bounds {
                low: 0,
                high: Some(float.format.greatest()),
            };
            for constructor in wrappers {
                self.built
                    .push((slot(self.program, constructor, 0), pattern));
            }
            answer = answer.or(pattern);
        }
        answer
    }

    /// The natural a binding is outright, where it is one.
    fn exact(&self, binding: ExprId) -> Option<u128> {
        match self.program.expr(binding) {
            Expr::Static(value) => match self.program.constant(value).view() {
                super::ConstantView::Natural(number) => u128::try_from(number.to_biguint()).ok(),
                _ => None,
            },
            Expr::Atom(a) => self.exact[a.0.index()],
            _ => None,
        }
    }

    /// What a term answers, held against the term so that the tier below
    /// has it where it walks.
    fn expr(&mut self, id: ExprId) -> Bounds {
        let held = self.worked(id);
        self.terms[id.index()] = self.terms[id.index()].or(held);
        held
    }

    fn worked(&mut self, id: ExprId) -> Bounds {
        match self.program.expr(id) {
            Expr::Atom(atom) => self.scope[atom.0.index()],
            Expr::Static(value) => {
                let value = self.program.constant(value);
                self.constant_fields(value);
                constant_bounds(self.program, value)
            }
            Expr::Con(ctor, args) => {
                for (at, atom) in self.program.atoms(args).iter().enumerate() {
                    let place = slot(self.program, ctor, at);
                    self.built.push((place, self.scope[atom.0.index()]));
                }
                self.built(ctor, args)
            }
            Expr::Call(called, args) => self.call(called, args),
            Expr::Match(scrutinee, arms) => {
                self.matched[id.index()] =
                    self.matched[id.index()].or(self.scope[scrutinee.0.index()]);
                self.branch(scrutinee.0.index(), arms)
            }
        }
    }

    fn call(&mut self, called: FnId, args: Range) -> Bounds {
        let held: Vec<Bounds> = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| self.scope[atom.0.index()])
            .collect();
        let operation_of = self.operations.get(called.index()).copied().flatten();
        let sequence_of = self.sequences.get(called.index()).copied().flatten();
        let answer = match (operation_of, sequence_of) {
            (Some(op), _) => operation(self.program, op, held[0], held[1]),
            (None, Some(op)) => self.sequence(op, &held),
            (None, None) => self.results[called.index()].unwrap_or(Bounds::NOTHING),
        };
        let answer = self.claimed(called, args, answer);
        self.calls.push((called, held));
        if self
            .program
            .ctors(self.program.function(called).result)
            .is_empty()
        {
            Bounds::NOTHING
        } else {
            answer
        }
    }

    /// How many elements a recognized sequence operation answers, or its
    /// length: worked out here from what its operands hold, as arithmetic
    /// is, rather than from its definition, which is answered for every
    /// call at once. Replacing keeps a length, appending adds one, putting
    /// one before another adds theirs, dropping takes the count away and
    /// taking keeps the fewer.
    fn sequence(&self, op: SequenceOperation, held: &[Bounds]) -> Bounds {
        let counted = match op {
            SequenceOperation::Length | SequenceOperation::Replace => held[0],
            SequenceOperation::Append => held[0].up(),
            SequenceOperation::ReverseOnto | SequenceOperation::Prepend => held[0].plus(held[1]),
            SequenceOperation::Drop => held[0].monus(held[1]),
            SequenceOperation::Take => fewer(held[0], held[1]),
        };
        let length = self.assumed.length.unwrap_or(Bounds::ANY);
        // On a way nothing reaches, what any length can be: a definition
        // handed only that is still handed a length, which a word holds.
        if counted.is_nothing() {
            return length;
        }
        counted.and(length)
    }

    /// Record what a known value holds in each field, all the way down. A
    /// spine is read as a count, not field by field, so what one holds is
    /// said to be anything.
    fn constant_fields(&mut self, value: super::Constant<'_>) {
        let super::ConstantView::Constructor(ctor) = value.view() else {
            if let super::ConstantView::Spine(spine) = value.view() {
                self.spine_fields(value.owner(), spine);
            }
            return;
        };
        let mut budget = super::Budget::new(super::FoldLimits {
            work: u64::MAX,
            work_per_function: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let fields = ctor
            .fields(&mut budget)
            .expect("validated constants can be revisited");
        for (at, field) in fields.into_iter().enumerate() {
            let place = slot(self.program, ctor.constructor(), at);
            self.built
                .push((place, constant_bounds(self.program, field)));
            self.constant_fields(field);
        }
    }

    /// A run of bytes holds each byte in its element field. A short spine
    /// of anything else is read element by element, as a constructor's
    /// fields are; a long one is not, so its fields could hold anything.
    fn spine_fields(&mut self, owner: TypeId, spine: super::SpineView<'_>) {
        let Shape::Spine {
            cons, recursive, ..
        } = shape(self.program, owner)
        else {
            self.outside.push(owner);
            return;
        };
        let Some(bytes) = spine.to_bytes() else {
            if spine.length() > ELEMENTS_READ.into() {
                self.outside.push(owner);
            } else {
                self.spine_elements(spine, cons, recursive);
            }
            return;
        };
        let (Some(&low), Some(&high)) = (bytes.iter().min(), bytes.iter().max()) else {
            return;
        };
        let element = usize::from(recursive == 0);
        self.built.push((
            slot(self.program, cons, element),
            Bounds {
                low: u64::from(low),
                high: Some(u64::from(high)),
            },
        ));
    }

    /// Each element's fields of a constant spine, built into `cons`.
    fn spine_elements(&mut self, spine: super::SpineView<'_>, cons: CtorId, recursive: usize) {
        let mut budget = super::Budget::new(super::FoldLimits {
            work: u64::MAX,
            work_per_function: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let elements = spine
            .elements(&mut budget)
            .expect("validated constants can be revisited");
        for fields in elements {
            for (at, field) in fields.into_iter().enumerate() {
                let at = if at >= recursive { at + 1 } else { at };
                self.built.push((
                    slot(self.program, cons, at),
                    constant_bounds(self.program, field),
                ));
                self.constant_fields(field);
            }
        }
    }

    /// A number's empty constructor is nought and its other one is one more
    /// than what it wraps. A tag is which constructor it is.
    fn built(&self, ctor: CtorId, args: Range) -> Bounds {
        let owner = self.program.ctor(ctor).owner;
        if single_field(self.program, owner).is_some() {
            let promised = self.assumed.field(ctor, 0);
            return self
                .program
                .atoms(args)
                .first()
                .map_or(Bounds::ANY, |atom| self.scope[atom.0.index()])
                .and(promised);
        }
        let Shape::Spine { nil, recursive, .. } = shape(self.program, owner) else {
            return Bounds::at(u64::from(self.program.tag(ctor)));
        };
        if ctor == nil {
            return Bounds::at(0);
        }
        // A number, or how many elements a sequence holds: one more than
        // the rest.
        self.program
            .atoms(args)
            .get(recursive)
            .map_or(Bounds::ANY, |atom| self.scope[atom.0.index()].up())
    }

    /// Each arm in turn, with what the constructor it matched says of the
    /// value it took apart. What the match holds is what any arm holds.
    fn branch(&mut self, scrutinee: usize, arms: Range) -> Bounds {
        let mut answer = None;
        let outer = self.scope.clone();
        let predicates = self.predicates.clone();
        let exact = self.exact.clone();
        let mut surviving: Option<Vec<Bounds>> = None;
        for arm in self.program.arms(arms) {
            self.scope.clone_from(&outer);
            self.predicates.clone_from(&predicates);
            self.exact.clone_from(&exact);
            let level = self.scope.len();
            if !self.enter(scrutinee, arm.ctor) {
                continue;
            }
            let found = self.body(arm.body);
            answer = Some(answer.map_or(found, |held: Bounds| held.or(found)));
            if !found.is_nothing() {
                let inner = &self.scope[..level];
                if let Some(surviving) = &mut surviving {
                    for (held, found) in surviving.iter_mut().zip(inner) {
                        *held = held.or(*found);
                    }
                } else {
                    surviving = Some(inner.to_vec());
                }
            }
        }
        self.scope = surviving.unwrap_or(outer);
        self.predicates = predicates;
        self.exact = exact;
        // Where no arm is reached, nothing is: a value nothing knows yet is
        // a value no constructor could have built.
        answer.unwrap_or(Bounds::NOTHING)
    }

    fn enter(&mut self, scrutinee: usize, ctor: CtorId) -> bool {
        let held = self.scope[scrutinee];
        let owner = self.program.ctor(ctor).owner;
        let spine = shape(self.program, owner);
        if !reaches(self.program, held, spine, ctor) {
            return false;
        }
        let binding = if single_field(self.program, owner).is_some() {
            let promised = self.assumed.field(ctor, 0);
            Binding::Whole(held.and(promised))
        } else {
            match spine {
                Shape::Spine { nil, .. } if ctor == nil => {
                    self.scope[scrutinee] = Bounds::at(0);
                    Binding::Whole(Bounds::NOTHING)
                }
                Shape::Spine { recursive, .. } => {
                    self.scope[scrutinee] = Bounds {
                        low: held.low.max(1),
                        high: held.high,
                    };
                    Binding::Built(Some((recursive, self.scope[scrutinee].down())))
                }
                Shape::Tagged => {
                    self.scope[scrutinee] = Bounds::at(u64::from(self.program.tag(ctor)));
                    Binding::Built(None)
                }
            }
        };
        self.bind_fields(ctor, binding);
        if let Some((op, left, right)) = self.predicates[scrutinee] {
            let (a, b) = refine(op, ctor, self.scope[left], self.scope[right]);
            self.scope[left] = a;
            self.scope[right] = b;
            if a.is_nothing() || b.is_nothing() {
                return false;
            }
        }
        self.predicates.resize(self.scope.len(), None);
        self.exact.resize(self.scope.len(), None);
        true
    }

    /// Bind a constructor's fields. A field holds what was built into it --
    /// nothing yet, where no walk has built one -- and one whose type is a
    /// run of bare tags is one of them besides: the type says that much
    /// alone. The rest of a spine is one step down its count instead.
    fn bind_fields(&mut self, ctor: CtorId, binding: Binding) {
        for (at, &ty) in self.program.fields(ctor).iter().enumerate() {
            let counted = match binding {
                Binding::Whole(held) => Some(held),
                Binding::Built(Some((recursive, rest))) if recursive == at => Some(rest),
                Binding::Built(_) => None,
            };
            if let Some(held) = counted {
                self.scope.push(held);
                continue;
            }
            let built = self.fields[slot(self.program, ctor, at)].unwrap_or(Bounds::NOTHING);
            self.scope
                .push(tag_count(self.program, ty).map_or(built, |count| {
                    built.and(Bounds {
                        low: 0,
                        high: Some(count - 1),
                    })
                }));
        }
    }
}

/// The fewer of two counts, each anywhere in its bounds.
fn fewer(a: Bounds, b: Bounds) -> Bounds {
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let high = match (a.high, b.high) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (Some(high), None) | (None, Some(high)) => Some(high),
        (None, None) => None,
    };
    Bounds {
        low: a.low.min(b.low),
        high,
    }
}

/// How many tags a type has, where its constructors all carry nothing and
/// there are at least two of them: a value of one is a tag below this.
fn tag_count(program: &Program, ty: TypeId) -> Option<u64> {
    (super::type_shape(program, ty) == super::TypeShape::Enumeration)
        .then(|| u64::try_from(program.ctors(ty).len()).expect("a count of constructors"))
}

fn constant_bounds(program: &Program, value: super::Constant<'_>) -> Bounds {
    let value = super::single_field_constant(program, value);
    match value.view() {
        super::ConstantView::Natural(number) => number.try_u64().map_or(Bounds::ANY, Bounds::at),
        super::ConstantView::Constructor(ctor)
            if program
                .ctors(value.owner())
                .iter()
                .all(|c| program.types_of(c.fields).is_empty()) =>
        {
            Bounds::at(u64::from(program.tag(ctor.constructor())))
        }
        super::ConstantView::Spine(spine) => {
            u64::try_from(spine.length()).map_or(Bounds::ANY, Bounds::at)
        }
        super::ConstantView::Constructor(_) => Bounds::ANY,
    }
}

fn operation(program: &Program, op: super::Operation, a: Bounds, b: Bounds) -> Bounds {
    use super::Operation;
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let (yes, no, decided) = match op {
        Operation::Add => return a.plus(b),
        Operation::Monus => return a.monus(b),
        Operation::Mul => return a.times(b),
        Operation::Div => return a.quotient(b),
        Operation::Mod => return a.remainder(b),
        Operation::And => return a.masked(b),
        Operation::Or => return a.merged(b, true),
        Operation::Xor => return a.merged(b, false),
        Operation::Pow => return a.power(b),
        Operation::Equals { yes, no } => (
            yes,
            no,
            if a.high == Some(a.low) && b.high == Some(b.low) {
                Some(a.low == b.low)
            } else if a.high.is_some_and(|a| a < b.low) || b.high.is_some_and(|b| b < a.low) {
                Some(false)
            } else {
                None
            },
        ),
        Operation::LessThan { yes, no } => (
            yes,
            no,
            if a.high.is_some_and(|a| a < b.low) {
                Some(true)
            } else if b.high.is_some_and(|b| a.low >= b) {
                Some(false)
            } else {
                None
            },
        ),
    };
    let yes = Bounds::at(u64::from(program.tag(yes)));
    let no = Bounds::at(u64::from(program.tag(no)));
    decided.map_or_else(|| yes.or(no), |held| if held { yes } else { no })
}

fn exclude(held: Bounds, other: Bounds) -> Bounds {
    if other.high != Some(other.low) {
        return held;
    }
    if held.low == other.low {
        return held.and(Bounds {
            low: held.low.saturating_add(1),
            high: None,
        });
    }
    if held.high == Some(other.low) {
        return held.and(Bounds {
            low: 0,
            high: other.low.checked_sub(1),
        });
    }
    held
}

fn refine(op: super::Operation, ctor: CtorId, a: Bounds, b: Bounds) -> (Bounds, Bounds) {
    use super::Operation;
    match op {
        Operation::Equals { yes, .. } if ctor == yes => (a.and(b), b.and(a)),
        Operation::Equals { .. } => (exclude(a, b), exclude(b, a)),
        Operation::LessThan { yes, .. } if ctor == yes => {
            let a_limit = b.high.map_or(Bounds::ANY, |high| {
                high.checked_sub(1).map_or(Bounds::NOTHING, |high| Bounds {
                    low: 0,
                    high: Some(high),
                })
            });
            (
                a.and(a_limit),
                b.and(Bounds {
                    low: a.low.saturating_add(1),
                    high: None,
                }),
            )
        }
        Operation::LessThan { .. } => (
            a.and(Bounds {
                low: b.low,
                high: None,
            }),
            b.and(Bounds {
                low: 0,
                high: a.high,
            }),
        ),
        _ => (a, b),
    }
}
