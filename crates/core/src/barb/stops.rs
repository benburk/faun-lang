//! Whether every definition stops.
//!
//! A definition may go round only on something it took apart, so each time
//! round is over something strictly smaller and the taking apart has an
//! end. What that takes is two things: knowing, of every value a body
//! holds, what it is against the parameters it came from; and knowing, of
//! every way round the call graph, that something gets smaller.
//!
//! What a call does to the sizes it carries is read into a matrix -- rows
//! are the parameters it was handed and columns are the arguments it hands
//! on. Size-change termination closes those matrices under composition. Every
//! idempotent path from a definition back to itself must have a strict
//! decrease on its diagonal; such a path can repeat, but its decreasing value
//! cannot do so forever.
//!
//! Where that finds a way round on which nothing gets smaller, a round may
//! still close a gap: a loop counting `i` up to `n`, a search moving `lo`
//! toward `hi`. The matrices then carry a measure besides each parameter,
//! `a ∸ b` for each ordered pair of natural parameters, which gets smaller
//! where the new pair lies within the old, one side has moved, and a guard
//! keeps them apart. What guards say is read in [`super::relations`].
//!
//! Where that still finds nothing, what calls answer is read too: each
//! definition's answer against its parameters, worked out as a greatest
//! fixpoint, and taken apart as its shape says, so a parser answering
//! `Ok((value, rest))` goes round on a `rest` no longer than its input. A
//! field of a parameter is then a size of its own, so an answer handed to a
//! definition that takes it apart carries what its fields are.
//!
//! A list's depth counts what it holds, so a list rebuilt around elements a
//! call made says nothing of how deep it is. Its length is read beside it:
//! each list a definition takes is a row of its own, and what a body holds
//! is bounded by one of those lengths, or two together, plus a constant. A
//! rest is one shorter and a cons one longer, whatever the element, and a
//! call answers its summary with each list in it replaced by what was
//! handed for it, so `[f(x), *map(rest)]` is no longer than what `map` took.
//! Two together is what a walk building onto an accumulator answers,
//! `reverse_into(xs, built)`, which is how `reverse` and the walks turning
//! what they built round at the end are seen to answer no more than they
//! took. A summary starts
//! with every set of lists as small as anything and each is weakened until
//! it holds, so the sum survives where neither list alone does.
//!
//! A natural is on the same scale, its value its length, so a count and a
//! list compare: `len(xs)` is as long as `xs`, `take(xs, n)` no longer than
//! either, and `drop(xs, n)` shorter than `xs` where `n` is at least one and
//! `xs` is not empty. Division, subtraction and a remainder say what they
//! say of numbers there too. How long a list at least is comes from the
//! constructors it was matched as, a match on its rest included, so past
//! `sort([])` and `sort([x])` a list holds two, its half by `len / 2` is at
//! least one, and both halves `split_at` answers are shorter than it. A
//! call of a small definition going round nowhere, as `split_at` does, is
//! read in place with what its arguments are there, rather than by what it
//! answers for anything.
//!
//! A number a guard keeps at or above another is at least as large as that
//! one is known to be, so past `n < 10` a tenth of `n` is smaller. A product
//! of something at least one by something at least two is more than it,
//! and a recognized operation worked out again on the same operands is the
//! same value, so what a guard said of `tenths * 10` holds of the product
//! handed on.
//!
//! Closure can be much larger than the source call graph. Barb keeps matrices
//! flat and indexes graphs by both endpoints, so a new graph is composed only
//! with graphs that can actually precede or follow it. A failing idempotent is
//! reported as soon as it appears rather than after the closure is complete.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::model::{Atom, Body, Expr, ExprId, FnId};
use super::program::Program;
use super::relations::{self, EQUAL, Facts, GREATER, LESS, Value, Verdict};
use super::{ConstantView, Operation, Refusal, SequenceOperation};

/// What a value is, against a parameter it came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Step {
    /// Taken out of it, and so strictly smaller than it.
    Smaller,
    /// It, or something else no bigger and no smaller.
    Same,
    /// Nothing that can be said. What a call answers is this, until
    /// something says what a call answers.
    Unknown,
}

/// A local's constructor depth relative to one parameter. Keeping the
/// distance until a call matrix is built lets `Succ(m)` retain one decrease
/// after `m` was taken through two constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bound {
    Unknown,
    /// No deeper than the parameter plus this signed distance.
    Offset(i64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocalFacts {
    bounds: Vec<Bound>,
    /// A proven lower bound on its size, capped at two: a natural's value,
    /// or how many elements a list has.
    minimum: u8,
    /// No shallower than each parameter plus this distance, where known:
    /// the other side of `bounds`, which a measure closing from below needs.
    lower: Vec<Option<i64>>,
    /// The local whose value this is, which facts are stated of.
    same: Option<usize>,
    /// What each constructor it may be says, where it is a verdict.
    verdict: Option<Verdict>,
    /// What it is taken apart as, where something says.
    shape: Shape,
    /// How long it is, where it is a list: at most the lengths of each
    /// [`Spines`] key's parameters together, plus this. Empty where
    /// nothing is known, and otherwise one entry per key, each already the
    /// least any smaller key says.
    lengths: Vec<Option<i64>>,
    /// The natural it is, where it is known outright.
    exact: Option<u64>,
    /// The local whose rest this is, where an arm took one apart: what is
    /// learned of this one's length is learned of that one's.
    rest_of: Option<usize>,
}

/// What a value is taken apart as: for each constructor it may be, what its
/// fields are. A parser answering `Ok((value, rest))` says of `rest`, in
/// the `Ok` it answers, that it is no longer than what it was handed.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    /// Nothing is known of which constructor it is.
    Unknown,
    /// As small as anything, which a summary not yet worked out assumes of
    /// a call, and what reading its body then weakens.
    Least,
    Known(Rc<Vec<(super::CtorId, Vec<LocalFacts>)>>),
}

impl Shape {
    /// What a value is, whichever of two it was: the constructors either
    /// may be, each with what both say of its fields where both say.
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Least, held) | (held, Self::Least) => held.clone(),
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Known(a), Self::Known(b)) => {
                let mut joined: Vec<_> = a
                    .iter()
                    .map(|(ctor, fields)| {
                        let fields = b.iter().find(|(other, _)| other == ctor).map_or_else(
                            || fields.clone(),
                            |(_, others)| {
                                fields.iter().zip(others).map(|(a, b)| a.join(b)).collect()
                            },
                        );
                        (*ctor, fields)
                    })
                    .collect();
                joined.extend(
                    b.iter()
                        .filter(|(ctor, _)| !a.iter().any(|(held, _)| held == ctor))
                        .cloned(),
                );
                // In one order, so one shape is one value.
                joined.sort_by_key(|(ctor, _)| ctor.index());
                Self::Known(Rc::new(joined))
            }
        }
    }
}

/// The range a summary's distances are kept in, and how deep its shapes
/// go, so that working one out reaches an end.
const LEAST_OFFSET: i64 = -2;
const MOST_OFFSET: i64 = 4;
const SHAPE_DEPTH: usize = 3;

/// The lists a definition takes, whose lengths what it holds is read
/// against: each parameter whose type is a spine. A natural is one too, its
/// length its value, so a count and a list are read on one scale: what
/// `len` answers is as long as its list, and `take(xs, n)` no longer than
/// `n`.
///
/// A length is at most one of them, or two together, plus a constant: a
/// walk building onto what it was handed answers both, so that is as far as
/// `reverse_into` needs a key to reach. Each key is a set of them, in one
/// order, and a local holds one bound per key.
#[derive(Debug)]
struct Spines {
    params: Vec<usize>,
    /// Which of `params` each key holds, as bits, the empty key first.
    keys: Vec<u32>,
}

/// What reading lengths takes: each definition's lists, which definitions
/// are a sequence operation, answered by what it means rather than by its
/// body, and which call nothing going round and are small enough to read
/// in place at a call.
struct Lengths {
    spines: Vec<Spines>,
    sequences: Vec<Option<SequenceOperation>>,
    simple: Vec<bool>,
}

/// How many terms a definition read in place at a call may have, and how
/// deep such reading goes.
const MOST_READ_IN_PLACE: usize = 48;
const DEEPEST_IN_PLACE: usize = 3;

impl Lengths {
    fn of(program: &Program, operations: &[Option<Operation>]) -> Self {
        let count = program.functions().len();
        let spines = (0..count)
            .map(|at| Spines::of(program, FnId::at(at)))
            .collect();
        let sequences = super::arithmetic::recognise_sequences(program, operations);
        let calls = graph(program);
        let mut simple = vec![false; count];
        for round in rounds(&calls) {
            let &[id] = round.as_slice() else {
                continue;
            };
            let Some(body) = program.function(id).body() else {
                continue;
            };
            simple[id.index()] =
                !calls[id.index()].contains(&id) && terms(program, body) <= MOST_READ_IN_PLACE;
        }
        Self {
            spines,
            sequences,
            simple,
        }
    }
}

/// How many terms a body holds, its arms' included.
fn terms(program: &Program, body: Body) -> usize {
    let bindings = program.bindings(body.bindings);
    bindings
        .iter()
        .chain([&body.tail])
        .map(|&expr| match program.expr(expr) {
            Expr::Match(_, arms) => {
                1 + program
                    .arms(arms)
                    .iter()
                    .map(|arm| terms(program, arm.body))
                    .sum::<usize>()
            }
            Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) | Expr::Call(..) => 1,
        })
        .sum()
}

/// Where lengths are not read: no lists, and no keys.
static NO_SPINES: Spines = Spines {
    params: Vec::new(),
    keys: Vec::new(),
};

/// How many of a definition's lists its keys are made of.
const MOST_SPINES: usize = 8;

impl Spines {
    fn of(program: &Program, id: FnId) -> Self {
        let params: Vec<usize> = program
            .params(id)
            .iter()
            .enumerate()
            .filter(|(_, ty)| matches!(super::shape(program, **ty), super::Shape::Spine { .. }))
            .map(|(at, _)| at)
            .take(MOST_SPINES)
            .collect();
        let mut keys = vec![0];
        for one in 0..params.len() {
            keys.push(1 << one);
            for other in one + 1..params.len() {
                keys.push((1 << one) | (1 << other));
            }
        }
        keys.sort_unstable();
        Self { params, keys }
    }

    fn key(&self, bits: u32) -> Option<usize> {
        self.keys.binary_search(&bits).ok()
    }

    /// Each key's bound the least any key within it says: a list at most
    /// `a` long is at most `a` and `b` together long.
    fn close(&self, lengths: &mut [Option<i64>]) {
        if lengths.is_empty() {
            return;
        }
        for (at, &bits) in self.keys.iter().enumerate() {
            let within = self.keys[..at]
                .iter()
                .zip(lengths.iter())
                .filter(|(inner, _)| *inner & bits == **inner)
                .filter_map(|(_, bound)| *bound)
                .min();
            lengths[at] = match (lengths[at], within) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (held, None) | (None, held) => held,
            };
        }
    }

    /// Each key's bound, where it was built from bounds on the keys it was
    /// handed: the least each says, closed.
    fn gathered(&self, found: impl IntoIterator<Item = (u32, i64)>) -> Vec<Option<i64>> {
        let mut lengths = vec![None; self.keys.len()];
        for (bits, bound) in found {
            if let Some(at) = self.key(bits) {
                lengths[at] = Some(lengths[at].map_or(bound, |held: i64| held.min(bound)));
            }
        }
        self.close(&mut lengths);
        if lengths.iter().all(Option::is_none) {
            return Vec::new();
        }
        lengths
    }

    /// A parameter, as long as itself.
    fn parameter(&self, param: usize) -> Vec<Option<i64>> {
        self.params
            .iter()
            .position(|&held| held == param)
            .map_or_else(Vec::new, |at| self.gathered([(1 << at, 0)]))
    }

    /// What a summary of `id` not yet worked out assumes.
    fn least(&self, program: &Program, id: FnId) -> LocalFacts {
        LocalFacts::least(program.params(id).len(), self.keys.len())
    }

    /// A list exactly this long.
    fn exactly(&self, length: i64) -> Vec<Option<i64>> {
        self.gathered([(0, length)])
    }
}

/// Both bounds on one length: the lesser of each key's, where either says.
fn met_lengths(a: &[Option<i64>], b: &[Option<i64>]) -> Vec<Option<i64>> {
    if a.is_empty() {
        return b.to_vec();
    }
    if b.is_empty() {
        return a.to_vec();
    }
    a.iter()
        .zip(b)
        .map(|pair| match pair {
            (Some(a), Some(b)) => Some((*a).min(*b)),
            (held, None) | (None, held) => *held,
        })
        .collect()
}

/// A length bound kept to the range a summary holds.
fn clamped(bound: Option<i64>) -> Option<i64> {
    bound
        .filter(|bound| *bound <= MOST_OFFSET)
        .map(|bound| bound.max(LEAST_OFFSET))
}

/// Each bound moved by `by`.
fn shifted(lengths: &[Option<i64>], by: i64) -> Vec<Option<i64>> {
    lengths
        .iter()
        .map(|bound| bound.map(|bound| bound + by))
        .collect()
}

/// The keys a list's bounds say something new at: those no smaller key
/// already says as much at, which are all instantiating needs.
fn tightest(spines: &Spines, lengths: &[Option<i64>]) -> Vec<(u32, i64)> {
    spines
        .keys
        .iter()
        .zip(lengths)
        .enumerate()
        .filter_map(|(at, (&bits, &bound))| {
            let bound = bound?;
            let implied = spines.keys[..at]
                .iter()
                .zip(lengths)
                .any(|(&inner, &held)| {
                    inner & bits == inner && held.is_some_and(|held| held <= bound)
                });
            (!implied).then_some((bits, bound))
        })
        .collect()
}

impl LocalFacts {
    fn unknown(params: usize) -> Self {
        Self {
            bounds: vec![Bound::Unknown; params],
            minimum: 0,
            lower: vec![None; params],
            same: None,
            verdict: None,
            shape: Shape::Unknown,
            lengths: Vec::new(),
            exact: None,
            rest_of: None,
        }
    }

    /// What a summary not yet worked out assumes: as small as anything,
    /// under each of `keys`.
    fn least(params: usize, keys: usize) -> Self {
        Self {
            bounds: vec![Bound::Offset(LEAST_OFFSET); params],
            shape: Shape::Least,
            lengths: vec![Some(LEAST_OFFSET); keys],
            ..Self::unknown(params)
        }
    }

    /// What holds whichever of the two a body answered.
    fn join(&self, other: &Self) -> Self {
        Self {
            bounds: self
                .bounds
                .iter()
                .zip(&other.bounds)
                .map(|pair| match pair {
                    (Bound::Offset(a), Bound::Offset(b)) => Bound::Offset(*a.max(b)),
                    _ => Bound::Unknown,
                })
                .collect(),
            minimum: self.minimum.min(other.minimum),
            lower: self
                .lower
                .iter()
                .zip(&other.lower)
                .map(|(a, b)| a.zip(*b).map(|(a, b)| a.min(b)))
                .collect(),
            same: None,
            verdict: None,
            shape: self.shape.join(&other.shape),
            exact: self.exact.filter(|_| self.exact == other.exact),
            rest_of: None,
            // Each key's bound is the least that key says, so the larger of
            // two holds of either.
            lengths: if self.lengths.is_empty() || other.lengths.is_empty() {
                Vec::new()
            } else {
                self.lengths
                    .iter()
                    .zip(&other.lengths)
                    .map(|(a, b)| a.zip(*b).map(|(a, b)| a.max(b)))
                    .collect()
            },
        }
    }

    /// The same, kept to the range a summary holds and `depth` shapes deep.
    fn clamped(&self, depth: usize) -> Self {
        Self {
            bounds: self
                .bounds
                .iter()
                .map(|bound| match bound {
                    Bound::Offset(offset) if *offset <= MOST_OFFSET => {
                        Bound::Offset((*offset).max(LEAST_OFFSET))
                    }
                    _ => Bound::Unknown,
                })
                .collect(),
            minimum: self.minimum,
            lower: vec![None; self.lower.len()],
            same: None,
            verdict: None,
            shape: match &self.shape {
                Shape::Known(_) if depth == 0 => Shape::Unknown,
                Shape::Known(entries) => Shape::Known(Rc::new(
                    entries
                        .iter()
                        .map(|(ctor, fields)| {
                            (
                                *ctor,
                                fields
                                    .iter()
                                    .map(|field| field.clamped(depth - 1))
                                    .collect(),
                            )
                        })
                        .collect(),
                )),
                held => held.clone(),
            },
            lengths: self.lengths.iter().map(|bound| clamped(*bound)).collect(),
            exact: None,
            rest_of: None,
        }
    }

    /// A summary over a callee's parameters, read at a call: what is no
    /// deeper than a parameter there is no deeper than its argument here,
    /// and a list no longer than some of its lists together is no longer
    /// than what was handed for them.
    fn instantiated(&self, args: &[&Self], params: usize, ours: &Spines, theirs: &Spines) -> Self {
        let bounds = (0..params)
            .map(|row| {
                self.bounds
                    .iter()
                    .zip(args)
                    .filter_map(|(bound, arg)| match (bound, arg.bounds[row]) {
                        (Bound::Offset(a), Bound::Offset(b)) => Some(a + b),
                        _ => None,
                    })
                    .min()
                    .map_or(Bound::Unknown, Bound::Offset)
            })
            .collect();
        Self {
            bounds,
            minimum: self.minimum,
            shape: match &self.shape {
                Shape::Known(entries) => Shape::Known(Rc::new(
                    entries
                        .iter()
                        .map(|(ctor, fields)| {
                            let fields = fields
                                .iter()
                                .map(|field| field.instantiated(args, params, ours, theirs))
                                .collect();
                            (*ctor, fields)
                        })
                        .collect(),
                )),
                held => held.clone(),
            },
            lengths: self.handed_lengths(args, ours, theirs),
            ..Self::unknown(params)
        }
    }

    /// Each key of the callee's bound, with each list in it replaced by
    /// what its argument's bounds say: one sum for each way of picking a
    /// bound for each, kept where it is a key here. Every key the callee
    /// says anything at is read, not only the tightest: `a + 0` says less
    /// than `0` there, and more here where `a` was handed a list's rest.
    fn handed_lengths(&self, args: &[&Self], ours: &Spines, theirs: &Spines) -> Vec<Option<i64>> {
        let mut found = Vec::new();
        let said = theirs
            .keys
            .iter()
            .zip(&self.lengths)
            .filter_map(|(&bits, &bound)| Some((bits, bound?)));
        for (bits, bound) in said {
            let mut sums = vec![(0_u32, bound)];
            for (at, &param) in theirs.params.iter().enumerate() {
                if bits & (1 << at) == 0 {
                    continue;
                }
                let handed = tightest(ours, &args[param].lengths);
                sums = sums
                    .iter()
                    .flat_map(|&(held, sum)| {
                        handed
                            .iter()
                            // One list twice is not a key.
                            .filter(move |(bits, _)| held & bits == 0)
                            .map(move |&(bits, bound)| (held | bits, sum + bound))
                    })
                    .collect();
            }
            found.extend(sums);
        }
        ours.gathered(found)
    }

    /// Whichever says more of each row: both hold.
    fn meet(&self, other: &Self) -> Self {
        let mut met = self.clone();
        for (bound, other) in met.bounds.iter_mut().zip(&other.bounds) {
            *bound = match (*bound, *other) {
                (Bound::Offset(a), Bound::Offset(b)) => Bound::Offset(a.min(b)),
                (Bound::Unknown, known) | (known, Bound::Unknown) => known,
            };
        }
        met.minimum = met.minimum.max(other.minimum);
        met.lengths = met_lengths(&met.lengths, &other.lengths);
        met.exact = met.exact.or(other.exact);
        if met.shape == Shape::Unknown {
            met.shape = other.shape.clone();
        }
        met
    }
}

impl Step {
    /// Compose two legs of a path. An unknown leg breaks the fact; otherwise
    /// one strict leg makes the whole path strict.
    const fn then(self, next: Self) -> Self {
        match (self, next) {
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Smaller, _) | (_, Self::Smaller) => Self::Smaller,
            (Self::Same, Self::Same) => Self::Same,
        }
    }

    /// Keep the strongest of several paths between the same two values.
    const fn stronger(self, other: Self) -> Self {
        match (self, other) {
            (Self::Smaller, _) | (_, Self::Smaller) => Self::Smaller,
            (Self::Same, _) | (_, Self::Same) => Self::Same,
            (Self::Unknown, Self::Unknown) => Self::Unknown,
        }
    }
}

/// One call or composed path, from caller parameters to callee parameters.
/// Flat cells avoid the allocation per row used by the more general Ori
/// checker; Barb has no synthesized measures or row labels to retain.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Graph {
    caller: FnId,
    callee: FnId,
    rows: usize,
    columns: usize,
    cells: Vec<Step>,
}

impl Graph {
    fn at(&self, row: usize, column: usize) -> Step {
        self.cells[row * self.columns + column]
    }

    fn strict_diagonal(&self) -> bool {
        (0..self.rows.min(self.columns)).any(|at| self.at(at, at) == Step::Smaller)
    }

    fn idempotent(&self) -> bool {
        self.caller == self.callee && compose(self, self) == *self
    }
}

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

/// Refuse a definition nothing shows stops, naming the call that begins a
/// way round on which nothing gets smaller.
pub(super) fn stops(program: &Program) -> Result<(), Refusal> {
    let calls = graph(program);
    let operations = super::arithmetic::recognise(program);
    let mut summaries = None;
    for round in rounds(&calls) {
        // One definition on its own goes round only if it calls itself.
        if round.len() == 1 && !calls[round[0].index()].contains(&round[0]) {
            continue;
        }
        // What guards say, and the gaps they keep, are read only for a round
        // nothing else shows stops, and what definitions answer only for
        // one that still is not.
        let none = HashMap::new();
        if descends(program, &round, &operations, Tier::plain(&none)).is_ok()
            || descends(program, &round, &operations, Tier::measured(&none)).is_ok()
        {
            continue;
        }
        let (lengths, summaries) = summaries.get_or_insert_with(|| {
            let lengths = Lengths::of(program, &operations);
            let summaries = summaries_of(program, &operations, &lengths);
            (lengths, summaries)
        });
        descends(
            program,
            &round,
            &operations,
            Tier::answered(summaries, lengths),
        )?;
    }
    Ok(())
}

/// What each definition answers against its parameters, as far as its
/// body shows: the greatest fixpoint, each round assumed to answer as
/// little as anything and weakened until what its bodies answer under the
/// assumption is what was assumed. What a call answers is only said of a
/// call that answers, which is all a proof of stopping reads it for: the
/// facts of one step round, where the rest has already come back.
fn summaries_of(
    program: &Program,
    operations: &[Option<Operation>],
    lengths: &Lengths,
) -> HashMap<FnId, LocalFacts> {
    let calls = graph(program);
    let mut summaries = HashMap::new();
    for round in rounds(&calls) {
        let bodied: Vec<FnId> = round
            .into_iter()
            .filter(|id| program.function(*id).body().is_some())
            .collect();
        for &id in &bodied {
            summaries.insert(id, lengths.spines[id.index()].least(program, id));
        }
        let mut settled = false;
        for _ in 0..64 {
            let mut changed = false;
            for &id in &bodied {
                let answered = summarised(
                    program,
                    id,
                    operations,
                    Tier::summarised(&summaries, lengths),
                );
                if summaries.get(&id) != Some(&answered) {
                    summaries.insert(id, answered);
                    changed = true;
                }
            }
            if !changed {
                settled = true;
                break;
            }
        }
        // Only a fixpoint says anything.
        if !settled {
            for id in &bodied {
                summaries.remove(id);
            }
        }
    }
    summaries
}

/// What `id` answers under what a tier assumes of every definition.
fn summarised(
    program: &Program,
    id: FnId,
    operations: &[Option<Operation>],
    tier: Tier<'_>,
) -> LocalFacts {
    Reader::new(program, id, &HashSet::new(), operations, tier)
        .answer()
        .clamped(SHAPE_DEPTH)
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
        // In the order they were written, which is the order a round reads
        // in and the order its matrices are built in.
        round.sort_unstable_by_key(|held| held.index());
        self.held.push(round);
    }
}

/// Close the call matrices and require every repeatable path to descend.
/// How much a round is read for: plainly; with the gaps between its
/// parameters measured and its guards read; and besides that with what its
/// calls answer, taken apart where their answers are handed on, and how
/// long the lists they answer are, which a summary is worked out with too.
#[derive(Clone, Copy)]
struct Tier<'a> {
    measured: bool,
    pathed: bool,
    summaries: &'a HashMap<FnId, LocalFacts>,
    /// What lengths are read with, where they are.
    lengths: Option<&'a Lengths>,
}

impl<'a> Tier<'a> {
    const fn plain(summaries: &'a HashMap<FnId, LocalFacts>) -> Self {
        Self {
            measured: false,
            pathed: false,
            summaries,
            lengths: None,
        }
    }

    const fn measured(summaries: &'a HashMap<FnId, LocalFacts>) -> Self {
        Self {
            measured: true,
            pathed: false,
            summaries,
            lengths: None,
        }
    }

    const fn summarised(summaries: &'a HashMap<FnId, LocalFacts>, lengths: &'a Lengths) -> Self {
        Self {
            measured: true,
            pathed: false,
            summaries,
            lengths: Some(lengths),
        }
    }

    const fn answered(summaries: &'a HashMap<FnId, LocalFacts>, lengths: &'a Lengths) -> Self {
        Self {
            measured: true,
            pathed: true,
            summaries,
            lengths: Some(lengths),
        }
    }
}

fn descends(
    program: &Program,
    round: &[FnId],
    operations: &[Option<Operation>],
    measured: Tier<'_>,
) -> Result<(), Refusal> {
    let within: HashSet<FnId> = round.iter().copied().collect();
    let direct = round.iter().flat_map(|id| {
        program.function(*id).body().map_or_else(Vec::new, |_| {
            let mut reader = Reader::new(program, *id, &within, operations, measured);
            reader.answer();
            reader.held
        })
    });
    let Err((function, call)) = Closure::new().proves(direct) else {
        return Ok(());
    };

    let named: Vec<&str> = round
        .iter()
        .map(|id| program.name(program.function(*id).name))
        .collect();
    Err(Refusal {
        message: format!("nothing here shows `{}` stops", named.join("`, `")),
        function: Some(function),
        call: Some(call),
        label: Some("goes round on what it was handed, not on a part of it".to_owned()),
        help: Some(
            "hand each round a part of what it was handed, such as a list's rest, so it gets \
             smaller until it stops"
                .to_owned(),
        ),
    })
}

/// The finite closure of one component's size-change graphs.
///
/// The endpoint indexes are authoritative only for entries in `graphs`; an
/// insertion updates all three together. IDs in each index are increasing,
/// which lets `products` pair a graph only with earlier entries and avoid
/// recomputing every ordered pair as the closure grows.
struct Closure {
    graphs: Vec<Graph>,
    /// The direct call each graph's path begins with, by graph.
    first_calls: Vec<ExprId>,
    seen: HashSet<Graph>,
    by_caller: HashMap<FnId, Vec<usize>>,
    by_callee: HashMap<FnId, Vec<usize>>,
}

impl Closure {
    fn new() -> Self {
        Self {
            graphs: Vec::new(),
            first_calls: Vec::new(),
            seen: HashSet::new(),
            by_caller: HashMap::new(),
            by_callee: HashMap::new(),
        }
    }

    /// Close the direct graphs, each beside the call it was read from, or
    /// answer where a path with no descent begins: its definition and call.
    fn proves(
        mut self,
        direct: impl IntoIterator<Item = (Graph, ExprId)>,
    ) -> Result<(), (FnId, ExprId)> {
        for (graph, call) in direct {
            self.insert(graph, call)?;
        }

        let mut at = 0;
        while at < self.graphs.len() {
            for (product, call) in self.products(at) {
                self.insert(product, call)?;
            }
            at += 1;
        }
        Ok(())
    }

    /// Add one unique graph whose path begins with `call`, or report an
    /// idempotent path with no descent by where it begins.
    fn insert(&mut self, graph: Graph, call: ExprId) -> Result<(), (FnId, ExprId)> {
        if !self.seen.insert(graph.clone()) {
            return Ok(());
        }
        if !graph.strict_diagonal() && graph.idempotent() {
            return Err((graph.caller, call));
        }

        let at = self.graphs.len();
        self.by_caller.entry(graph.caller).or_default().push(at);
        self.by_callee.entry(graph.callee).or_default().push(at);
        self.graphs.push(graph);
        self.first_calls.push(call);
        Ok(())
    }

    /// Compose `at` in both orders with compatible graphs already processed.
    fn products(&self, at: usize) -> Vec<(Graph, ExprId)> {
        let graph = &self.graphs[at];
        let mut products = Vec::new();

        for &before in self.by_callee.get(&graph.caller).into_iter().flatten() {
            if before > at {
                break;
            }
            products.push((
                compose(&self.graphs[before], graph),
                self.first_calls[before],
            ));
        }
        for &after in self.by_caller.get(&graph.callee).into_iter().flatten() {
            if after >= at {
                break;
            }
            products.push((compose(graph, &self.graphs[after]), self.first_calls[at]));
        }
        products
    }
}

/// Compose paths `a → b` and `b → c`.
fn compose(first: &Graph, second: &Graph) -> Graph {
    debug_assert_eq!(first.callee, second.caller);
    debug_assert_eq!(first.columns, second.rows);

    let mut cells = vec![Step::Unknown; first.rows * second.columns];
    for row in 0..first.rows {
        for column in 0..second.columns {
            let mut best = Step::Unknown;
            for middle in 0..first.columns {
                best = best.stronger(first.at(row, middle).then(second.at(middle, column)));
            }
            cells[row * second.columns + column] = best;
        }
    }
    Graph {
        caller: first.caller,
        callee: second.callee,
        rows: first.rows,
        columns: second.columns,
        cells,
    }
}

/// A field of a parameter, as a size of its own: what a callee takes apart
/// of its argument, where the caller built or was answered that argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Path {
    param: usize,
    ctor: super::CtorId,
    field: usize,
}

/// How many fields of its parameters a definition is read as having.
const MOST_PATHS: usize = 16;

/// The fields of a definition's parameters of sums that do not hold
/// themselves, where they are read: `Found(text, rest)` handed in, `rest`
/// is a size of its own.
fn paths(program: &Program, id: FnId, pathed: bool) -> Vec<Path> {
    if !pathed {
        return Vec::new();
    }
    let mut held = Vec::new();
    for (param, &ty) in program.params(id).iter().enumerate() {
        if !matches!(
            super::type_shape(program, ty),
            super::TypeShape::Sum
                | super::TypeShape::Product { .. }
                | super::TypeShape::Wrapper { .. }
        ) {
            continue;
        }
        let owner = program.ctors(ty);
        let recursive = owner
            .iter()
            .any(|ctor| program.types_of(ctor.fields).contains(&ty));
        if recursive {
            continue;
        }
        for tag in 0..owner.len() {
            let ctor = program.ctor_at(ty, u32::try_from(tag).expect("a tag fits"));
            for field in 0..program.fields(ctor).len() {
                held.push(Path { param, ctor, field });
            }
        }
    }
    held.truncate(MOST_PATHS);
    held
}

/// The top of a measured gap: a natural parameter, or a number a body binds
/// before anything else, which is the same every time round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Top {
    Parameter(usize),
    Number { value: u64, local: usize },
}

/// The gaps `top ∸ bottom` a round may close in a definition, where it is
/// measured: between each two of its natural parameters, and from each number
/// its body first binds down to each natural parameter. A parameter every
/// call hands one value is that value inside, once optimized, and a guard
/// then compares with the number rather than the parameter.
fn measures(program: &Program, id: FnId, measured: bool) -> Vec<(Top, usize)> {
    if !measured {
        return Vec::new();
    }
    let params = program.params(id);
    let naturals: Vec<usize> = params
        .iter()
        .enumerate()
        .filter(|(_, ty)| super::arithmetic::natural(program, **ty).is_some())
        .map(|(at, _)| at)
        .collect();
    let numbers = program.function(id).body().map_or_else(Vec::new, |body| {
        program
            .bindings(body.bindings)
            .iter()
            .enumerate()
            .filter_map(|(at, &binding)| {
                let Expr::Static(value) = program.expr(binding) else {
                    return None;
                };
                let ConstantView::Natural(value) = program.constant(value).view() else {
                    return None;
                };
                Some(Top::Number {
                    value: value.try_u64().ok()?,
                    local: params.len() + at,
                })
            })
            .collect()
    });
    let tops = naturals.iter().map(|&at| Top::Parameter(at)).chain(numbers);
    tops.flat_map(|top| {
        naturals
            .iter()
            .filter(move |&&bottom| top != Top::Parameter(bottom))
            .map(move |&bottom| (top, bottom))
    })
    .collect()
}

/// What one definition's body says of the sizes it hands on: a graph per
/// call it makes to one it goes round with, beside that call, and what it
/// answers.
struct Reader<'a> {
    program: &'a Program,
    from: FnId,
    within: &'a HashSet<FnId>,
    operations: &'a [Option<Operation>],
    /// Whether gaps between parameters are measured, and guards read.
    measured: bool,
    /// What each definition answers, where that has been worked out.
    summaries: &'a HashMap<FnId, LocalFacts>,
    params: usize,
    /// The fields of parameters read as sizes of their own, which follow
    /// the parameters among the rows every bound is kept over.
    paths: Vec<Path>,
    rows: usize,
    /// Whether any definition's fields are read so.
    pathed: bool,
    /// What lengths are read with, where they are, and this definition's
    /// lists. Where a matrix is built, each of its lists has a row of its
    /// own after the fields, its length.
    lengths: Option<&'a Lengths>,
    own: &'a Spines,
    /// How many calls deep in others this body is read, where a call of a
    /// definition going round nowhere is read in place.
    depth: usize,
    locals: Vec<LocalFacts>,
    held: Vec<(Graph, ExprId)>,
    /// What the guards around the part being read say.
    facts: Facts,
    /// Each recognized operation already worked out in scope, by what it
    /// was handed, and the local holding it: working one out again is the
    /// same value, so what a guard said of the first holds of the second.
    computed: Vec<(FnId, Vec<Operand>, usize)>,
}

/// An operand of a recognized operation, as far as telling two alike goes:
/// whose value it is, or the number it is.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Operand {
    Local(usize),
    Number(u64),
}

impl<'a> Reader<'a> {
    fn new(
        program: &'a Program,
        from: FnId,
        within: &'a HashSet<FnId>,
        operations: &'a [Option<Operation>],
        tier: Tier<'a>,
    ) -> Self {
        let params = program.params(from).len();
        let paths = paths(program, from, tier.pathed);
        let own = tier
            .lengths
            .map_or(&NO_SPINES, |lengths| &lengths.spines[from.index()]);
        let lists = if tier.pathed { own.params.len() } else { 0 };
        let rows = params + paths.len() + lists;
        // A parameter starts at distance zero from itself. Distances are
        // kept through local construction and become the three-valued
        // matrix only at an in-round call.
        let locals = (0..params)
            .map(|at| {
                let mut facts = LocalFacts::unknown(rows);
                facts.bounds[at] = Bound::Offset(0);
                facts.lower[at] = Some(0);
                facts.same = Some(at);
                facts.lengths = own.parameter(at);
                facts
            })
            .collect();
        Self {
            program,
            from,
            within,
            operations,
            measured: tier.measured,
            summaries: tier.summaries,
            params,
            paths,
            rows,
            pathed: tier.pathed,
            lengths: tier.lengths,
            own,
            depth: 0,
            locals,
            held: Vec::new(),
            facts: Vec::new(),
            computed: Vec::new(),
        }
    }

    /// What the body answers, reading it whole.
    fn answer(&mut self) -> LocalFacts {
        let body = self
            .program
            .function(self.from)
            .body()
            .expect("a definition read has a body");
        self.read(body)
    }
}

impl Reader<'_> {
    /// Each binding takes the next level, and what an arm takes apart is
    /// one constructor smaller than its scrutinee. What it answers.
    fn read(&mut self, body: Body) -> LocalFacts {
        for &binding in self.program.bindings(body.bindings) {
            let mut facts = self.term(binding);
            if facts.same.is_none() {
                facts.same = Some(self.locals.len());
            }
            self.locals.push(facts);
        }
        self.term(body.tail)
    }

    fn term(&mut self, id: ExprId) -> LocalFacts {
        let unknown = LocalFacts::unknown(self.rows);
        match self.program.expr(id) {
            Expr::Atom(atom) => self.locals.get(atom.0.index()).cloned().unwrap_or(unknown),
            Expr::Static(value) => self.constant(value),
            Expr::Con(ctor, args) => {
                let args = self.program.atoms(args);
                let mut built = constructed(self.program, ctor, args, &self.locals, unknown);
                built.lengths = self.built_length(ctor, args);
                // A constructor of nothing is as small as a value is, so no
                // bigger than any parameter.
                if self.measured && args.is_empty() {
                    built.bounds = vec![Bound::Offset(0); self.rows];
                }
                built
            }
            Expr::Call(to, args) => self.call(id, to, self.program.atoms(args)),
            Expr::Match(scrutinee, arms) => {
                let answered = self.arms(scrutinee, arms);
                let mut matched = self.matched(id);
                if let Some(answered) = answered {
                    let verdict = matched.verdict.take();
                    matched = LocalFacts {
                        verdict,
                        ..answered
                    };
                }
                matched
            }
        }
    }

    /// A value known outright is its constructor, whatever its fields are,
    /// and a list known outright is as long as it is.
    fn constant(&self, value: super::ConstId) -> LocalFacts {
        let ctor = self.program.constant(value).constructor();
        let fields = self.program.fields(ctor).len();
        let (length, exact) = match self.program.constant(value).view() {
            ConstantView::Spine(spine) => (i64::try_from(spine.length()).ok(), None),
            ConstantView::Natural(natural) => {
                let exact = natural.try_u64().ok();
                (exact.and_then(|exact| i64::try_from(exact).ok()), exact)
            }
            ConstantView::Constructor(_) => (None, None),
        };
        let lengths = length.map_or_else(
            || self.built_length(ctor, &[]),
            |length| self.own.exactly(length),
        );
        let minimum = length.map_or(0, |length| {
            u8::try_from(length.clamp(0, 2)).expect("at most two")
        });
        LocalFacts {
            minimum,
            lengths,
            exact,
            shape: Shape::Known(Rc::new(vec![(
                ctor,
                vec![LocalFacts::unknown(self.rows); fields],
            )])),
            ..LocalFacts::unknown(self.rows)
        }
    }

    /// A call: a graph where it goes round, what recognized arithmetic says
    /// of its answer, and the verdict it answers where it answers one.
    fn call(&mut self, id: ExprId, to: FnId, args: &[Atom]) -> LocalFacts {
        if self.within.contains(&to) {
            let graph = self.matrix(to, args);
            self.held.push((graph, id));
        }
        let mut result = if let Some(operation) = self.operations[to.index()] {
            let unknown = LocalFacts::unknown(self.rows);
            let mut result = self.arithmetic(operation, args, unknown);
            result.same = self.recomputed(to, args);
            result
        } else {
            self.answered(to, args)
        };
        if self.measured {
            let values = self.values(args);
            if let Value::Verdict(verdict) =
                relations::called(self.program, self.operations, to, &values)
            {
                result.verdict = Some(verdict);
            }
        }
        result
    }

    /// The local already holding what a recognized operation works out of
    /// these operands, where one does; otherwise this one is noted as the
    /// next local, which it becomes where it is bound.
    fn recomputed(&mut self, to: FnId, args: &[Atom]) -> Option<usize> {
        let operands: Vec<Operand> = args
            .iter()
            .map(|arg| {
                let at = arg.0.index();
                self.locals[at]
                    .exact
                    .map_or_else(|| Operand::Local(self.same(at)), Operand::Number)
            })
            .collect();
        let found = self
            .computed
            .iter()
            .find(|(callee, handed, _)| *callee == to && *handed == operands)
            .map(|&(_, _, at)| at);
        if found.is_none() {
            self.computed.push((to, operands, self.locals.len()));
        }
        found
    }

    /// What a call answers: what its summary says with what was handed,
    /// and besides that what a sequence operation means, or what its body
    /// says read in place.
    fn answered(&self, to: FnId, args: &[Atom]) -> LocalFacts {
        let unknown = LocalFacts::unknown(self.rows);
        let summarised = self.summaries.get(&to).map_or(unknown, |summary| {
            let args: Vec<&LocalFacts> =
                args.iter().map(|arg| &self.locals[arg.0.index()]).collect();
            let theirs = self
                .lengths
                .map_or(&NO_SPINES, |lengths| &lengths.spines[to.index()]);
            summary.instantiated(&args, self.rows, self.own, theirs)
        });
        let read = self
            .sequence(to, args)
            .or_else(|| self.read_in_place(to, args));
        match read {
            Some(read) => read.meet(&summarised),
            None => summarised,
        }
    }

    /// What a sequence operation answers, by what it means: how many a
    /// list holds is as long as it, its first `n` are no longer than it or
    /// than `n`, and it without some of its first, where there are some to
    /// take, is shorter than it.
    fn sequence(&self, to: FnId, args: &[Atom]) -> Option<LocalFacts> {
        let operation = (*self.lengths?.sequences.get(to.index())?)?;
        let list = &self.locals[args.first()?.0.index()];
        let unknown = LocalFacts::unknown(self.rows);
        match operation {
            SequenceOperation::Length => Some(LocalFacts {
                bounds: list.bounds.clone(),
                minimum: list.minimum,
                lengths: list.lengths.clone(),
                ..unknown
            }),
            SequenceOperation::Take => {
                let count = &self.locals[args.get(1)?.0.index()];
                Some(LocalFacts {
                    bounds: list.bounds.clone(),
                    minimum: list.minimum.min(self.minimum(args[1].0.index())),
                    lengths: met_lengths(&list.lengths, &count.lengths),
                    ..unknown
                })
            }
            SequenceOperation::Drop => Some(self.dropped(list, args.get(1)?.0.index())),
            SequenceOperation::ReverseOnto
            | SequenceOperation::Prepend
            | SequenceOperation::Append
            | SequenceOperation::Replace => None,
        }
    }

    /// A list without its first `count`: a part of it, and a strict one
    /// where there are some to take and it takes at least one.
    fn dropped(&self, list: &LocalFacts, count: usize) -> LocalFacts {
        let strict = self.minimum(count) >= 1 && list.minimum >= 1;
        let by = i64::from(strict);
        let dropped = self.locals[count].exact.map_or(2, |exact| exact.min(2));
        LocalFacts {
            bounds: list
                .bounds
                .iter()
                .map(|bound| match bound {
                    Bound::Offset(offset) => Bound::Offset(offset - by),
                    Bound::Unknown => Bound::Unknown,
                })
                .collect(),
            minimum: list
                .minimum
                .saturating_sub(u8::try_from(dropped).expect("at most two")),
            lengths: shifted(&list.lengths, -by),
            ..LocalFacts::unknown(self.rows)
        }
    }

    /// What a call of a definition going round nowhere answers, its body
    /// read here with what its arguments are here: what it answers for
    /// these, rather than what it answers for anything.
    fn read_in_place(&self, to: FnId, args: &[Atom]) -> Option<LocalFacts> {
        let lengths = self.lengths?;
        // Only where stopping is being shown: working out what every
        // definition answers, round after round, would read each callee
        // again every time.
        if !self.pathed && self.depth == 0
            || self.depth >= DEEPEST_IN_PLACE
            || !lengths.simple.get(to.index()).copied().unwrap_or(false)
            || self.within.contains(&to)
        {
            return None;
        }
        let body = self.program.function(to).body()?;
        let locals = args
            .iter()
            .enumerate()
            .map(|(at, arg)| LocalFacts {
                same: Some(at),
                rest_of: None,
                ..self.locals[arg.0.index()].clone()
            })
            .collect();
        let mut inner = Reader {
            program: self.program,
            from: to,
            within: self.within,
            operations: self.operations,
            measured: self.measured,
            summaries: self.summaries,
            params: args.len(),
            paths: Vec::new(),
            rows: self.rows,
            pathed: false,
            lengths: self.lengths,
            own: self.own,
            depth: self.depth + 1,
            locals,
            held: Vec::new(),
            facts: Vec::new(),
            computed: Vec::new(),
        };
        let answer = inner.read(body);
        debug_assert!(inner.held.is_empty(), "nothing read in place goes round");
        Some(answer)
    }

    /// What a match answers, which is a verdict where its arms answer them.
    fn matched(&self, id: ExprId) -> LocalFacts {
        let unknown = LocalFacts::unknown(self.rows);
        if !self.measured {
            return unknown;
        }
        let mut env: Vec<Value> = (0..self.locals.len()).map(|at| self.value(at)).collect();
        match relations::evaluated(self.program, self.operations, id, &mut env) {
            Value::Verdict(verdict) => LocalFacts {
                verdict: Some(verdict),
                ..unknown
            },
            Value::Size(_) | Value::Unknown => unknown,
        }
    }

    /// Each arm read under what its constructor says of the scrutinee, and
    /// an arm the scrutinee's verdict or shape cannot reach not read at all.
    /// What the arms answer, whichever answered.
    fn arms(&mut self, scrutinee: Atom, arms: super::Range) -> Option<LocalFacts> {
        let at = scrutinee.0.index();
        let mut answered: Option<LocalFacts> = None;
        for arm in self.program.arms(arms) {
            let Some((shaped, given)) = self.reached(at, arm.ctor) else {
                continue;
            };
            let (level, facts) = (self.locals.len(), self.facts.len());
            let minimums = self.minimums(at);
            self.bind_fields(at, arm.ctor, shaped.as_deref());
            self.facts.extend(given);
            let arm_answer = self.read(arm.body);
            self.facts.truncate(facts);
            self.locals.truncate(level);
            self.computed.retain(|&(_, _, at)| at < level);
            for (held, minimum) in minimums {
                self.locals[held].minimum = minimum;
            }
            answered = Some(match answered {
                None => arm_answer,
                Some(before) => before.join(&arm_answer),
            });
        }
        answered
    }

    /// Whether an arm for `ctor` can be reached from what local `at` is,
    /// and if so, what its shape says of the fields and its verdict of the
    /// sizes around.
    fn reached(&self, at: usize, ctor: super::CtorId) -> Option<(Option<Vec<LocalFacts>>, Facts)> {
        let count = self.program.fields(ctor).len();
        let shaped = match &self.locals[at].shape {
            Shape::Unknown => None,
            Shape::Least => Some(vec![
                LocalFacts::least(self.rows, self.own.keys.len());
                count
            ]),
            Shape::Known(entries) => Some(
                entries
                    .iter()
                    .find(|(held, _)| *held == ctor)
                    .map(|(_, fields)| fields.clone())?,
            ),
        };
        let given = match &self.locals[at].verdict {
            Some(verdict) if self.measured => {
                let tag = usize::try_from(self.program.tag(ctor)).expect("a tag fits");
                verdict.outcomes[tag].clone()?
            }
            _ => Vec::new(),
        };
        Some((shaped, given))
    }

    /// The fields an arm for `ctor` binds of local `at`: one constructor
    /// smaller than it, what its shape says besides, and a field of a
    /// parameter read as a size of its own that size.
    fn bind_fields(&mut self, at: usize, ctor: super::CtorId, shaped: Option<&[LocalFacts]>) {
        let level = self.locals.len();
        let successor = natural_successor(self.program, ctor);
        let pushed = pushed_rest(self.program, ctor);
        if pushed.is_some() {
            self.lengthen(at, 1);
        }
        let field = taken(&self.locals[at], successor);
        self.locals
            .resize(level + self.program.fields(ctor).len(), field);
        // The rest of a list is one shorter than it, and what is learned of
        // how long it is is learned of the list too.
        if let Some(rest) = pushed {
            let minimum = self.locals[at].minimum.saturating_sub(1);
            let lengths = shifted(&self.locals[at].lengths, -1);
            let local = &mut self.locals[level + rest];
            local.minimum = minimum;
            local.rest_of = Some(at);
            if !self.own.keys.is_empty() {
                local.lengths = lengths;
            }
        }
        let param = self.locals[at].same.filter(|&same| same < self.params);
        for (offset, local) in self.locals[level..].iter_mut().enumerate() {
            if let Some(shaped) = shaped.and_then(|fields| fields.get(offset)) {
                *local = local.meet(shaped);
            }
            if let Some(row) = param.and_then(|param| {
                self.paths.iter().position(|path| {
                    path.param == param && path.ctor == ctor && path.field == offset
                })
            }) {
                local.bounds[self.params + row] = Bound::Offset(0);
            }
            local.same = Some(level + offset);
        }
    }

    /// Local `at` known at least `least` long, and each list it is the
    /// rest of one longer than that.
    fn lengthen(&mut self, at: usize, least: u8) {
        let mut at = at;
        let mut least = least.min(2);
        while self.locals[at].minimum < least {
            self.locals[at].minimum = least;
            let Some(whole) = self.locals[at].rest_of else {
                break;
            };
            at = whole;
            least = least.saturating_add(1).min(2);
        }
    }

    /// The least length of `at` and of each list it is the rest of, to be
    /// put back when an arm that learned more is left.
    fn minimums(&self, at: usize) -> Vec<(usize, u8)> {
        let mut held = vec![(at, self.locals[at].minimum)];
        let mut at = at;
        while let Some(whole) = self.locals[at].rest_of {
            held.push((whole, self.locals[whole].minimum));
            at = whole;
        }
        held
    }

    /// How long a list `ctor` builds is: nothing at all, or one more than
    /// its rest.
    fn built_length(&self, ctor: super::CtorId, args: &[Atom]) -> Vec<Option<i64>> {
        if self.own.keys.is_empty() {
            return Vec::new();
        }
        match super::shape(self.program, self.program.ctor(ctor).owner) {
            super::Shape::Spine { nil, .. } if nil == ctor => self.own.exactly(0),
            super::Shape::Spine { recursive, .. } => {
                args.get(recursive).map_or_else(Vec::new, |rest| {
                    shifted(&self.locals[rest.0.index()].lengths, 1)
                })
            }
            super::Shape::Tagged => Vec::new(),
        }
    }

    /// Whose value a local is.
    fn same(&self, at: usize) -> usize {
        self.locals[at].same.unwrap_or(at)
    }

    fn value(&self, at: usize) -> Value {
        self.locals[at]
            .verdict
            .clone()
            .map_or_else(|| Value::Size(self.same(at)), Value::Verdict)
    }

    fn values(&self, args: &[Atom]) -> Vec<Value> {
        args.iter().map(|atom| self.value(atom.0.index())).collect()
    }

    /// The least a natural is: what built it says, or a guard placing it
    /// above something, since no size is below nought.
    fn minimum(&self, at: usize) -> u8 {
        let same = self.same(at);
        let mut least = self.locals[at].minimum;
        for fact in &self.facts {
            // How this stands to the other side, as the guard left it.
            let (other, rel) = if fact.left == same {
                (fact.right, fact.rel)
            } else if fact.right == same {
                let flipped = (fact.rel & EQUAL)
                    | if fact.rel & LESS == 0 { 0 } else { GREATER }
                    | if fact.rel & GREATER == 0 { 0 } else { LESS };
                (fact.left, flipped)
            } else {
                continue;
            };
            // At least what it is no less than, and one more where it is
            // more.
            if rel & LESS == 0 {
                let base = self.locals.get(other).map_or(0, |other| other.minimum);
                let strict = u8::from(rel & EQUAL == 0);
                least = least.max(base.saturating_add(strict).min(2));
            }
        }
        least
    }

    /// Bounds guaranteed by structurally recognized natural arithmetic.
    /// These are semantic properties of the recognized equations, not
    /// source-level names.
    fn arithmetic(
        &self,
        operation: Operation,
        args: &[Atom],
        mut result: LocalFacts,
    ) -> LocalFacts {
        let argument = |at: usize| &self.locals[args[at].0.index()];
        let minimum = |at: usize| self.minimum(args[at].0.index());
        let candidates: &[(&LocalFacts, bool)] = match operation {
            Operation::Monus => &[(argument(0), minimum(0) > 0 && minimum(1) > 0)],
            Operation::Div => &[(argument(0), minimum(0) > 0 && minimum(1) >= 2)],
            Operation::Mod => &[(argument(0), false), (argument(1), minimum(1) > 0)],
            Operation::And => &[(argument(0), false), (argument(1), false)],
            Operation::Add => {
                result.lower = self.grown(operation, args);
                result.lengths = self.summed(&argument(0).lengths, &argument(1).lengths);
                result.minimum = minimum(0).saturating_add(minimum(1)).min(2);
                return result;
            }
            Operation::Mul => {
                result.lower = self.grown(operation, args);
                return result;
            }
            Operation::Or
            | Operation::Xor
            | Operation::Pow
            | Operation::Equals { .. }
            | Operation::LessThan { .. } => return result,
        };
        for row in 0..result.bounds.len() {
            result.bounds[row] = candidates
                .iter()
                .filter_map(|(argument, strict)| match argument.bounds[row] {
                    Bound::Unknown => None,
                    Bound::Offset(offset) => Some(offset - i64::from(*strict)),
                })
                .min()
                .map_or(Bound::Unknown, Bound::Offset);
        }
        self.sized(operation, args, candidates, &mut result);
        result
    }

    /// What recognized arithmetic says on the length scale: no larger than
    /// a candidate, and smaller where it is strictly so; and halving by a
    /// known number keeps a least value.
    fn sized(
        &self,
        operation: Operation,
        args: &[Atom],
        candidates: &[(&LocalFacts, bool)],
        result: &mut LocalFacts,
    ) {
        for (argument, strict) in candidates {
            let bounded = shifted(&argument.lengths, -i64::from(*strict));
            result.lengths = met_lengths(&result.lengths, &bounded);
        }
        if operation == Operation::Div
            && let Some(divisor) = self.locals[args[1].0.index()]
                .exact
                .filter(|&divisor| divisor > 0)
        {
            let least = u64::from(self.minimum(args[0].0.index())) / divisor;
            result.minimum = u8::try_from(least).unwrap_or(0);
        }
    }

    /// A bound on the sum of two lengths: each way of picking one bound of
    /// each, kept where the two keys share no list.
    fn summed(&self, left: &[Option<i64>], right: &[Option<i64>]) -> Vec<Option<i64>> {
        let (left, right) = (tightest(self.own, left), tightest(self.own, right));
        let sums = left.iter().flat_map(|&(a, first)| {
            right
                .iter()
                .filter(move |(b, _)| a & b == 0)
                .map(move |&(b, second)| (a | b, first + second))
        });
        self.own.gathered(sums)
    }

    /// How far a sum or a product is above each parameter: a sum is at
    /// least either side and the other's least, and a product at least a
    /// side whose other is no less than one.
    fn grown(&self, operation: Operation, args: &[Atom]) -> Vec<Option<i64>> {
        let (left, right) = (args[0].0.index(), args[1].0.index());
        let from = |side: usize, other: usize, row: usize| {
            let lower = self.locals[side].lower[row]?;
            match operation {
                Operation::Add => Some(lower + i64::from(self.minimum(other))),
                // A product of a side at least one by at least two is more
                // than the side.
                _ if self.minimum(other) >= 2 && self.minimum(side) >= 1 => Some(lower + 1),
                _ => (self.minimum(other) >= 1).then_some(lower),
            }
        };
        (0..self.rows)
            .map(
                |row| match (from(left, right, row), from(right, left, row)) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (a, b) => a.or(b),
                },
            )
            .collect()
    }

    /// What one call hands on, read off the bounds of what it hands.
    fn matrix(&self, to: FnId, args: &[Atom]) -> Graph {
        let ours = measures(self.program, self.from, self.measured);
        let theirs = measures(self.program, to, self.measured);
        let their_paths = paths(self.program, to, self.pathed);
        let their_lists: &[usize] = match self.lengths {
            Some(lengths) if self.pathed => &lengths.spines[to.index()].params,
            _ => &[],
        };
        let rows = self.rows + ours.len();
        let columns = args.len() + their_paths.len() + their_lists.len() + theirs.len();
        let mut cells = vec![Step::Unknown; rows * columns];
        self.handed_sizes(&mut cells, columns, args, &their_paths);
        let lists = args.len() + their_paths.len();
        for (at, &param) in their_lists.iter().enumerate() {
            for row in 0..self.rows {
                cells[row * columns + lists + at] = self.handed_list(args[param], row);
            }
        }
        let past = lists + their_lists.len();
        for (row, &(top, bottom)) in ours.iter().enumerate() {
            for (column, &(handed, under)) in theirs.iter().enumerate() {
                let handed = match handed {
                    Top::Parameter(at) => Top::Parameter(args[at].0.index()),
                    number @ Top::Number { .. } => number,
                };
                cells[(self.rows + row) * columns + past + column] =
                    self.closes((top, bottom), (handed, args[under].0.index()), &ours);
            }
        }
        Graph {
            caller: self.from,
            callee: to,
            rows,
            columns,
            cells,
        }
    }

    /// How deep each argument is against each row here, and each field of
    /// one the callee reads as a size of its own.
    fn handed_sizes(
        &self,
        cells: &mut [Step],
        columns: usize,
        args: &[Atom],
        their_paths: &[Path],
    ) {
        for (column, arg) in args.iter().enumerate() {
            let Some(facts) = self.locals.get(arg.0.index()) else {
                continue;
            };
            for (row, bound) in facts.bounds.iter().enumerate() {
                cells[row * columns + column] = step(*bound);
            }
        }
        for (at, path) in their_paths.iter().enumerate() {
            if let Some(field) = self.handed_field(args, path) {
                for (row, bound) in field.bounds.iter().enumerate().take(self.rows) {
                    cells[row * columns + args.len() + at] = step(*bound);
                }
            }
        }
    }

    /// How long a list handed on is against a row here: no longer than it
    /// is deep, and no longer than its lengths say against a list here.
    fn handed_list(&self, arg: Atom, row: usize) -> Step {
        let facts = &self.locals[arg.0.index()];
        let deep = step(facts.bounds[row]);
        let long = row
            .checked_sub(self.params + self.paths.len())
            .and_then(|list| self.own.key(1 << list))
            .and_then(|key| facts.lengths.get(key).copied().flatten())
            .map_or(Step::Unknown, |bound| step(Bound::Offset(bound)));
        deep.stronger(long)
    }

    /// A field the callee reads of its argument, as the argument's shape
    /// says it is.
    fn handed_field(&self, args: &[Atom], path: &Path) -> Option<&LocalFacts> {
        let Shape::Known(entries) = &self.locals[args[path.param].0.index()].shape else {
            return None;
        };
        entries
            .iter()
            .find(|(ctor, _)| *ctor == path.ctor)
            .and_then(|(_, fields)| fields.get(path.field))
    }

    /// What the gap `upper ∸ lower` handed on is against this definition's
    /// gap `top ∸ bottom`: no wider where `upper` is at most `top` and
    /// `lower` at least `bottom`, and narrower besides where one of them
    /// moved and a guard keeps the pair apart, so the old gap was not nought.
    /// A handed `upper` is a local here where it is a parameter's argument,
    /// and a number where it is the callee's own.
    fn closes(
        &self,
        (top, bottom): (Top, usize),
        (upper, lower): (Top, usize),
        own: &[(Top, usize)],
    ) -> Step {
        let lower_same = self.same(lower);
        let upper_same = self.holding(upper, own);
        let top_local = match top {
            Top::Parameter(at) => at,
            Top::Number { local, .. } => local,
        };
        let below = self.below(top, upper, upper_same);
        let built = match self.locals[lower].lower[bottom] {
            Some(offset) if offset >= 1 => Some(true),
            Some(0) => Some(false),
            _ => None,
        };
        let above = stronger(built, self.placed(bottom, lower_same));
        let (Some(below), Some(above)) = (below, above) else {
            return Step::Unknown;
        };
        let apart = upper_same
            .is_some_and(|upper| relations::holds(&self.facts, lower_same, upper, LESS))
            || relations::holds(&self.facts, bottom, top_local, LESS);
        if (below || above) && apart {
            Step::Smaller
        } else {
            Step::Same
        }
    }

    /// The local here holding what a handed gap's top is: the argument, or
    /// a number this body binds too.
    fn holding(&self, upper: Top, own: &[(Top, usize)]) -> Option<usize> {
        match upper {
            Top::Parameter(local) => Some(self.same(local)),
            Top::Number { value, .. } => own.iter().find_map(|(held, _)| match held {
                Top::Number { value: here, local } if *here == value => Some(*local),
                _ => None,
            }),
        }
    }

    /// Whether a handed top is no more than this gap's top, and if so
    /// whether it is less.
    fn below(&self, top: Top, upper: Top, upper_same: Option<usize>) -> Option<bool> {
        match (top, upper) {
            (Top::Parameter(a), Top::Parameter(local)) => {
                let built = match self.locals[local].bounds[a] {
                    Bound::Offset(offset) if offset < 0 => Some(true),
                    Bound::Offset(0) => Some(false),
                    _ => None,
                };
                stronger(built, upper_same.and_then(|upper| self.placed(upper, a)))
            }
            (Top::Number { value, .. }, Top::Number { value: handed, .. }) => {
                (handed <= value).then_some(handed < value)
            }
            (Top::Number { local, .. }, Top::Parameter(_)) => self.placed(upper_same?, local),
            (Top::Parameter(_), Top::Number { .. }) => None,
        }
    }

    /// Whether the guards place `left` at most `right`, and if so whether
    /// below it.
    fn placed(&self, left: usize, right: usize) -> Option<bool> {
        if relations::holds(&self.facts, left, right, LESS) {
            Some(true)
        } else if relations::holds(&self.facts, left, right, LESS | EQUAL) {
            Some(false)
        } else {
            None
        }
    }
}

/// Of two ways of placing one value against another, each "no more"
/// or "less" where it places it at all, the one saying more.
const fn stronger(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a || b),
        (held, None) | (None, held) => held,
    }
}

const fn step(bound: Bound) -> Step {
    match bound {
        Bound::Offset(offset) if offset < 0 => Step::Smaller,
        Bound::Offset(0) => Step::Same,
        Bound::Unknown | Bound::Offset(_) => Step::Unknown,
    }
}

/// What an arm binds of its scrutinee: one constructor smaller, and a
/// natural's predecessor exactly one below it.
fn taken(value: &LocalFacts, predecessor: bool) -> LocalFacts {
    LocalFacts {
        bounds: value
            .bounds
            .iter()
            .map(|bound| match bound {
                Bound::Unknown => Bound::Unknown,
                Bound::Offset(offset) => Bound::Offset(offset - 1),
            })
            .collect(),
        minimum: 0,
        lower: value
            .lower
            .iter()
            .map(|lower| lower.filter(|_| predecessor).map(|lower| lower - 1))
            .collect(),
        same: None,
        verdict: None,
        shape: Shape::Unknown,
        lengths: Vec::new(),
        exact: None,
        rest_of: None,
    }
}

/// A constructor adds one to the deepest field. A nullary constructor has no
/// useful bound against an arbitrary parameter.
fn constructed(
    program: &Program,
    ctor: super::CtorId,
    args: &[Atom],
    locals: &[LocalFacts],
    mut result: LocalFacts,
) -> LocalFacts {
    result.shape = Shape::Known(Rc::new(vec![(
        ctor,
        args.iter()
            .map(|arg| locals[arg.0.index()].clamped(SHAPE_DEPTH - 1))
            .collect(),
    )]));
    if args.is_empty() {
        return result;
    }
    for row in 0..result.bounds.len() {
        let deepest = args
            .iter()
            .map(|arg| locals[arg.0.index()].bounds[row])
            .try_fold(i64::MIN, |deepest, bound| match bound {
                Bound::Unknown => None,
                Bound::Offset(offset) => Some(deepest.max(offset)),
            });
        if let Some(deepest) = deepest {
            result.bounds[row] = Bound::Offset(deepest + 1);
        }
    }
    if let super::Shape::Spine {
        cons, recursive, ..
    } = super::shape(program, program.ctor(ctor).owner)
        && cons == ctor
    {
        let rest = &locals[args[recursive].0.index()];
        result.minimum = rest.minimum.saturating_add(1).min(2);
    }
    if natural_successor(program, ctor) {
        let taken = &locals[args[0].0.index()];
        result.lower = taken
            .lower
            .iter()
            .map(|lower| lower.map(|lower| lower + 1))
            .collect();
    }
    result
}

/// Which field of `ctor` is the rest of a spine, where it pushes one.
fn pushed_rest(program: &Program, ctor: super::CtorId) -> Option<usize> {
    match super::shape(program, program.ctor(ctor).owner) {
        super::Shape::Spine {
            cons, recursive, ..
        } if cons == ctor => Some(recursive),
        _ => None,
    }
}

fn natural_successor(program: &Program, ctor: super::CtorId) -> bool {
    super::arithmetic::natural(program, program.ctor(ctor).owner)
        .is_some_and(|(_, successor)| successor == ctor)
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
            if let Some(body) = program.function(id).body() {
                within(program, body, &mut held);
            }
            held
        })
        .collect()
}
