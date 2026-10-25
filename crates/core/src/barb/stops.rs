//! Whether every definition stops.
//!
//! Nothing refuses a program for this: `faun check --totality` lists each
//! round of calls [`unproved`] finds, and a pure one fails the check.
//!
//! A definition may go round only on something it took apart, so each time
//! round is over something strictly smaller and the taking apart has an
//! end. What that takes is two things: knowing, of every value a body
//! holds, how big it is against the parameters it came from; and knowing,
//! of every way round the call graph, that something gets smaller.
//!
//! A definition is read against its *measures*, each a size of one of its
//! parameters: how deep it is; how long, where it is a list or one
//! constructor wrapping a list, or its value, where it is a natural, which
//! is its depth too; and how deep a field of it is, where it is a sum
//! holding no more of itself. Every value a body
//! holds carries bounds against them: how deep it is and how long at most,
//! and how long at least, each at a key of none, one or two measures added
//! up, plus a constant. A constructor is one deeper than its deepest
//! field, a spine's push one longer than its rest, and what an arm takes
//! apart one shallower, and a rest one shorter, whatever the element.
//! Recognized arithmetic and sequence operations answer by what their
//! equations mean: a difference or a quotient no larger than what it came
//! from, a sum the two added, a power above its exponent, `take(xs, n)` no
//! longer than either, `drop(xs, n)` shorter where it takes at least one,
//! two lists put together as long as both, and an element written over as
//! long as it was. How long a list at least is follows the constructors it
//! was matched as, so past `[]` and `[x]` a list holds two and each half
//! `split_at(len / 2)` answers is shorter; and a take and a drop by one
//! count are the list between them, so past `[*init, last]` matching, the
//! `init` taken is shorter.
//!
//! What a call does to the sizes it carries is read into a matrix: a row
//! for each measure of the caller, a column for each of the callee, the
//! cell whether what was handed is smaller than, as big as, or unknown
//! against it. Size-change termination closes those matrices under
//! composition. Every idempotent path from a definition back to itself must
//! have a strict decrease on its diagonal; such a path can repeat, but its
//! decreasing value cannot do so forever.
//!
//! A round may also close a gap: a loop counting `i` up to `n`, a search
//! moving `lo` toward `hi`. The matrices then carry, besides the measures,
//! `(a + 1) ∸ b` for each ordered pair of naturals, smaller where the new
//! pair lies within the old, one side has moved, and a guard keeps `b` no
//! larger than `a`: counting up while `i <= n` stops as `i < n` does.
//! What guards say is read in [`super::relations`] and becomes bounds on
//! entering an arm: past `x < y`, `x` is at most what `y` is at most, less
//! one, and `y` at least what `x` is at least, and one. How much larger one
//! value can be than another is then the least, over every key, of the
//! first's upper bound less the second's lower, and a gap closes where the
//! pair handed on is no further apart and either pair is in order. A
//! recognized operation worked out again on the same operands is the same
//! value, so what a guard said of `tenths * 10` holds of the product handed
//! on.
//!
//! Where that still finds nothing, what calls answer is read too: each
//! definition's answer against its measures, worked out as a greatest
//! fixpoint, every bound first as small as anything and weakened until what
//! the body answers is what was assumed, so a walk building onto what it
//! was handed, `reverse_into(xs, built)`, is seen to answer both lengths
//! added up. An answer is taken apart as its shape says, so a parser
//! answering `Ok((value, rest))` goes round on a `rest` no longer than its
//! input. A join, the rest of a body a match goes on to past an arm that
//! may leave, is read knowing what every call of it hands it, so a list and
//! its rest handed apart are still one shorter than the other. A call of a
//! small definition going round nowhere is read in place, with what its
//! arguments are there, and what it learned of them on the way to each
//! constructor it answers is learned where that is taken apart: past
//! `xs.first()` answering `Ok`, `xs` holds one.
//!
//! A round of several may be entered at only some of them. A small one the
//! round only passes through, calling itself nowhere and called from
//! nowhere outside, is read in place where another of it calls it, so a
//! loop split across two definitions knows in the second what it learned
//! in the first, and each way round is read from a definition it is
//! entered at.
//!
//! Each round is read three times over at most, each reading more than the
//! last, and only where the one before found nothing: plainly, with gaps and
//! guards, and with answers. Closure can be much larger than the source
//! call graph, so matrices are flat and indexed by both endpoints, a
//! definition the round only passes through and not read in place is
//! composed away first, a new
//! graph is composed only with graphs that can precede or follow it, and a
//! failing idempotent is reported as soon as it appears.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::calls::{graph, rounds};
use super::model::{Atom, Body, Expr, ExprId, FnId};
use super::program::Program;
use super::relations::{self, EQUAL, Facts, GREATER, LESS, Value, Verdict};
use super::{ConstantView, Operation, SequenceOperation};

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
    Known(Rc<Vec<(super::CtorId, Vec<Local>)>>),
}

impl Shape {
    /// The same constructors, each field as `f` makes it.
    fn mapped(&self, f: impl Fn(&Local) -> Local) -> Self {
        match self {
            Self::Known(entries) => Self::Known(Rc::new(
                entries
                    .iter()
                    .map(|(ctor, fields)| (*ctor, fields.iter().map(&f).collect()))
                    .collect(),
            )),
            held => held.clone(),
        }
    }

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

/// A size a definition is read against: something of one of its
/// parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Measure {
    /// How deep it is.
    Depth(usize),
    /// How long it is: a list's elements, or a natural's value, which is
    /// its depth as well.
    Length(usize),
    /// How deep one field of it is, where it is that constructor, so an
    /// answer handed on to a definition taking it apart carries its fields.
    Field {
        param: usize,
        ctor: super::CtorId,
        field: usize,
    },
}

/// Upper or lower bounds on one size of a value, one per key of a frame:
/// the size against that key's measures added up, plus this. Empty where
/// nothing is known.
type Bounds = Vec<Option<i64>>;

/// What one definition is read against: its measures, the keys a bound is
/// kept at, and the gaps between its naturals, which are measured besides.
struct Frame {
    measures: Vec<Measure>,
    /// Which measures each key adds up, as bits: none, each one, and each
    /// two lengths together, so a walk building onto what it was handed can
    /// answer both. A key comes after every key it holds.
    keys: Vec<u64>,
    gaps: Vec<(Top, usize)>,
}

/// How many fields of its parameters a definition is read as having, and
/// how many of its lengths are added two together.
const MOST_FIELDS: usize = 16;
const MOST_SUMMED: usize = 8;

impl Frame {
    /// Each parameter's depth, a natural's being its value; where answers
    /// are read, each list's length, a list one constructor wraps being as
    /// long as that list, and where stopping is shown with them,
    /// each field of a parameter of a sum holding no more of itself; and
    /// where they are measured, the gaps between its naturals.
    fn of(program: &Program, id: FnId, tier: &Tier<'_>) -> Self {
        let params = program.params(id);
        let natural = |ty| super::arithmetic::natural(program, ty).is_some();
        let spine = |ty| matches!(super::shape(program, ty), super::Shape::Spine { .. });
        let primary = params.iter().enumerate().map(|(at, &ty)| {
            if natural(ty) {
                Measure::Length(at)
            } else {
                Measure::Depth(at)
            }
        });
        let answers = tier.answers.is_some();
        let fields = fields(program, params)
            .take(MOST_FIELDS)
            .filter(|_| answers && tier.showing);
        let lists = params
            .iter()
            .enumerate()
            .filter(|&(_, &ty)| answers && (spine(ty) && !natural(ty) || wraps_list(program, ty)))
            .map(|(at, _)| Measure::Length(at));
        let measures: Vec<Measure> = primary.chain(fields).chain(lists).collect();
        assert!(
            measures.len() < 64,
            "a definition has fewer than 64 measures"
        );
        let keys = keys(&measures, answers);
        let gaps = if tier.gaps {
            gaps(program, id)
        } else {
            Vec::new()
        };
        Self {
            measures,
            keys,
            gaps,
        }
    }

    fn key(&self, bits: u64) -> Option<usize> {
        self.keys.binary_search(&bits).ok()
    }

    /// Where the bound against measure `at` alone is.
    fn single(&self, at: usize) -> usize {
        self.key(1 << at).expect("every measure is a key")
    }

    /// Where the measure of `ctor`'s field `field` of parameter `param` is.
    fn field(&self, param: usize, ctor: super::CtorId, field: usize) -> Option<usize> {
        self.measures
            .iter()
            .position(|&measure| measure == Measure::Field { param, ctor, field })
    }

    /// Where a parameter's list length is, where it has one of its own.
    fn length(&self, param: usize) -> Option<usize> {
        self.measures
            .iter()
            .rposition(|&measure| measure == Measure::Length(param))
    }

    /// Upper bounds, each at its key the least any key it holds says: a
    /// size at most `a` is at most `a` and `b` together. A key holds no
    /// more than two measures, so the keys within are few.
    fn close(&self, bounds: &mut Bounds) {
        if bounds.is_empty() {
            return;
        }
        for at in 1..self.keys.len() {
            let mut within = bounds[0];
            let mut bits = self.keys[at];
            if bits.count_ones() > 1 {
                while bits != 0 {
                    within = lesser(
                        within,
                        bounds[self.single(
                            usize::try_from(bits.trailing_zeros()).expect("a bit of a word"),
                        )],
                    );
                    bits &= bits - 1;
                }
            }
            bounds[at] = lesser(bounds[at], within);
        }
    }

    /// Upper bounds built from bounds at keys, the least each says, closed.
    fn gathered(&self, found: impl IntoIterator<Item = (u64, i64)>) -> Bounds {
        let mut bounds = vec![None; self.keys.len()];
        for (bits, bound) in found {
            if let Some(at) = self.key(bits) {
                bounds[at] = lesser(bounds[at], Some(bound));
            }
        }
        self.close(&mut bounds);
        if bounds.iter().all(Option::is_none) {
            return Vec::new();
        }
        bounds
    }

    /// At most this, whatever anything is: so at every key.
    fn most(&self, size: i64) -> Bounds {
        vec![Some(size); self.keys.len()]
    }

    /// At least this: a lower bound says nothing of any other key.
    fn least(&self, size: i64) -> Bounds {
        let mut bounds = vec![None; self.keys.len()];
        bounds[0] = Some(size);
        bounds
    }

    /// Exactly measure `at`, as an upper bound, so at every key holding
    /// it; or as a lower bound, which says nothing of any other key.
    fn itself(&self, at: usize, upper: bool) -> Bounds {
        if upper {
            let held = |bits: &u64| (bits & (1 << at) != 0).then_some(0);
            self.keys.iter().map(held).collect()
        } else {
            let mut bounds = vec![None; self.keys.len()];
            bounds[self.single(at)] = Some(0);
            bounds
        }
    }

    /// The keys an upper bound says something new at: those no key it
    /// holds says as much at.
    fn tightest(&self, bounds: &Bounds) -> Vec<(u64, i64)> {
        self.keys
            .iter()
            .zip(bounds)
            .enumerate()
            .filter_map(|(at, (&bits, &bound))| {
                let bound = bound?;
                let implied = self.keys[..at].iter().zip(bounds).any(|(&inner, &held)| {
                    inner & bits == inner && held.is_some_and(|held| held <= bound)
                });
                (!implied).then_some((bits, bound))
            })
            .collect()
    }

    /// Upper bounds kept at a callee's keys, each measure there replaced by
    /// what `handed` says bounds it here: one sum for each way of picking a
    /// bound for each, kept where it is a key here.
    fn substituted(&self, theirs: &Self, bounds: &Bounds, handed: &[Vec<(u64, i64)>]) -> Bounds {
        let mut found = Vec::new();
        for (&bits, &bound) in theirs.keys.iter().zip(bounds) {
            let Some(bound) = bound else {
                continue;
            };
            let mut sums = vec![(0_u64, bound)];
            for (at, handed) in handed.iter().enumerate() {
                if bits & (1 << at) == 0 {
                    continue;
                }
                sums = sums
                    .iter()
                    .flat_map(|&(held, sum)| {
                        handed
                            .iter()
                            .filter(move |(bits, _)| held & bits == 0)
                            .map(move |&(bits, bound)| (held | bits, sum.saturating_add(bound)))
                    })
                    .collect();
            }
            found.extend(sums);
        }
        self.gathered(found)
    }

    /// Upper bounds on a sum of two sizes.
    fn summed(&self, left: &Bounds, right: &Bounds) -> Bounds {
        let (left, right) = (self.tightest(left), self.tightest(right));
        let sums = left.iter().flat_map(|&(a, first)| {
            right
                .iter()
                .filter(move |(b, _)| a & b == 0)
                .map(move |&(b, second)| (a | b, first.saturating_add(second)))
        });
        self.gathered(sums)
    }
}

/// Whether `ty` is one constructor holding only a list, which is as long
/// as the list: a heap kept in a list is measured as the list is.
fn wraps_list(program: &Program, ty: super::TypeId) -> bool {
    let super::TypeShape::Wrapper { field, .. } = super::type_shape(program, ty) else {
        return false;
    };
    let spine = matches!(super::shape(program, field), super::Shape::Spine { .. });
    spine && super::arithmetic::natural(program, field).is_none()
}

/// The keys a bound is kept at: none, each measure, and where answers are
/// read, each two lengths together, in an order putting a key after every
/// key it holds.
fn keys(measures: &[Measure], summed: bool) -> Vec<u64> {
    let mut keys = vec![0];
    keys.extend((0..measures.len()).map(|at| 1 << at));
    if summed {
        let lengths: Vec<usize> = (0..measures.len())
            .filter(|&at| matches!(measures[at], Measure::Length(_)))
            .take(MOST_SUMMED)
            .collect();
        for (at, &one) in lengths.iter().enumerate() {
            keys.extend(
                lengths[at + 1..]
                    .iter()
                    .map(|&other| (1 << one) | (1 << other)),
            );
        }
    }
    keys.sort_unstable();
    keys
}

/// The fields of parameters of sums that do not hold themselves, as
/// measures of their own: `Found(text, rest)` handed in, `rest` is a size.
fn fields<'a>(
    program: &'a Program,
    params: &'a [super::TypeId],
) -> impl Iterator<Item = Measure> + 'a {
    params.iter().enumerate().flat_map(move |(param, &ty)| {
        let taken = matches!(
            super::type_shape(program, ty),
            super::TypeShape::Sum
                | super::TypeShape::Product { .. }
                | super::TypeShape::Wrapper { .. }
        );
        let ctors = program.ctors(ty);
        let recursive = ctors
            .iter()
            .any(|ctor| program.types_of(ctor.fields).contains(&ty));
        let ctors = if taken && !recursive { ctors.len() } else { 0 };
        (0..ctors).flat_map(move |tag| {
            let ctor = program.ctor_at(ty, u32::try_from(tag).expect("a tag fits"));
            (0..program.fields(ctor).len()).map(move |field| Measure::Field { param, ctor, field })
        })
    })
}

/// The lesser of two upper bounds, either of which may say nothing.
fn lesser(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (held, None) | (None, held) => held,
    }
}

/// What holds of either of two: the weaker bound at each key, which is the
/// larger of two upper bounds and the lesser of two lower.
fn either(a: &Bounds, b: &Bounds, upper: bool) -> Bounds {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    a.iter()
        .zip(b)
        .map(|(a, b)| {
            a.zip(*b)
                .map(|(a, b)| if upper { a.max(b) } else { a.min(b) })
        })
        .collect()
}

/// What holds of both: the stronger bound at each key.
fn both(a: &Bounds, b: &Bounds, upper: bool) -> Bounds {
    if a.is_empty() {
        return b.clone();
    }
    if b.is_empty() {
        return a.clone();
    }
    a.iter()
        .zip(b)
        .map(|pair| match pair {
            (Some(a), Some(b)) => Some(if upper { (*a).min(*b) } else { (*a).max(*b) }),
            (held, None) | (None, held) => *held,
        })
        .collect()
}

/// Each bound moved by `by`.
fn shifted(bounds: &Bounds, by: i64) -> Bounds {
    bounds
        .iter()
        .map(|bound| bound.map(|bound| bound.saturating_add(by)))
        .collect()
}

/// An upper bound as a step against the measure it is kept at.
const fn step(bound: Option<i64>) -> Step {
    match bound {
        Some(bound) if bound < 0 => Step::Smaller,
        Some(0) => Step::Same,
        _ => Step::Unknown,
    }
}

/// What a body holds, against the parameters it came from.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Local {
    /// How deep it is, at most.
    deep: Bounds,
    /// How long it is at most, where it is a list or a natural, or one
    /// constructor wrapping a list, which is as long as the list.
    long: Bounds,
    /// How long it is at least: at nothing, a number, and at a measure,
    /// that measure and a number. Only a gap reads the second.
    least: Bounds,
    /// The local whose value this is, which facts are stated of.
    same: Option<usize>,
    /// What each constructor it may be says, where it is a verdict.
    verdict: Option<Verdict>,
    /// What it is taken apart as, where something says.
    shape: Shape,
    /// The list whose rest this is, where an arm took one apart: what is
    /// learned of how long this is is learned of that too.
    rest_of: Option<usize>,
    /// Where this is what a drop leaves of a list past a take of it by the
    /// same count, that take and the list: the two are the list between
    /// them, so what is learned of how long this is says the take is
    /// shorter than the list by as much.
    past: Option<Split>,
    /// Where it is one constructor, how long some locals here are at least:
    /// what a body read in place learned of what it was handed on the way
    /// to answering it, so `xs.first()` answering `Ok` says `xs` holds one.
    given: Vec<(super::CtorId, Lengths)>,
}

/// Locals and how long each is at least.
type Lengths = Vec<(usize, i64)>;

/// A list cut in two at one count: the local holding its first part, and
/// the list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Split {
    front: usize,
    whole: usize,
}

/// The range a summary's bounds are kept in, and how deep its shapes go,
/// so that working one out reaches an end.
const LEAST_OFFSET: i64 = -2;
const MOST_OFFSET: i64 = 4;
const SHAPE_DEPTH: usize = 3;

impl Local {
    const fn unknown() -> Self {
        Self {
            deep: Vec::new(),
            long: Vec::new(),
            least: Vec::new(),
            same: None,
            verdict: None,
            shape: Shape::Unknown,
            rest_of: None,
            past: None,
            given: Vec::new(),
        }
    }

    /// What a summary not yet worked out assumes: as small as anything.
    fn smallest(keys: usize) -> Self {
        Self {
            deep: vec![Some(LEAST_OFFSET); keys],
            long: vec![Some(LEAST_OFFSET); keys],
            shape: Shape::Least,
            ..Self::unknown()
        }
    }

    /// What holds whichever of two a body answered.
    fn join(&self, other: &Self) -> Self {
        Self {
            deep: either(&self.deep, &other.deep, true),
            long: either(&self.long, &other.long, true),
            least: either(&self.least, &other.least, false),
            shape: self.shape.join(&other.shape),
            given: self.given_either(other),
            ..Self::unknown()
        }
    }

    /// What being each constructor says whichever of two it is: what both
    /// say where either may be it, and what one says where the other
    /// cannot be.
    fn given_either(&self, other: &Self) -> Vec<(super::CtorId, Lengths)> {
        let mut ctors: Vec<super::CtorId> = self
            .given
            .iter()
            .chain(&other.given)
            .map(|&(ctor, _)| ctor)
            .collect();
        ctors.sort_by_key(|ctor| ctor.index());
        ctors.dedup();
        ctors
            .into_iter()
            .filter_map(|ctor| {
                let lengths = match (self.lengths(ctor), other.lengths(ctor)) {
                    (Some(mine), Some(theirs)) => mine
                        .iter()
                        .filter_map(|&(at, least)| {
                            let (_, other) = theirs.iter().find(|&&(held, _)| held == at)?;
                            Some((at, least.min(*other)))
                        })
                        .collect(),
                    (Some(only), None) if !other.may_be(ctor) => only.clone(),
                    (None, Some(only)) if !self.may_be(ctor) => only.clone(),
                    _ => return None,
                };
                (!lengths.is_empty()).then_some((ctor, lengths))
            })
            .collect()
    }

    /// How long locals are at least where it is `ctor`, where it says.
    fn lengths(&self, ctor: super::CtorId) -> Option<&Lengths> {
        self.given
            .iter()
            .find(|&&(held, _)| held == ctor)
            .map(|(_, lengths)| lengths)
    }

    /// Whether it may be `ctor`, as far as its shape says. A summary
    /// assumed as small as anything is no value at all.
    fn may_be(&self, ctor: super::CtorId) -> bool {
        match &self.shape {
            Shape::Unknown => true,
            Shape::Least => false,
            Shape::Known(entries) => entries.iter().any(|&(held, _)| held == ctor),
        }
    }

    /// What holds of it where both do.
    fn meet(&self, other: &Self) -> Self {
        Self {
            deep: both(&self.deep, &other.deep, true),
            long: both(&self.long, &other.long, true),
            least: both(&self.least, &other.least, false),
            shape: if self.shape == Shape::Unknown {
                other.shape.clone()
            } else {
                self.shape.clone()
            },
            given: if self.given.is_empty() {
                other.given.clone()
            } else {
                self.given.clone()
            },
            ..self.clone()
        }
    }

    /// Its value on the length scale, where it is a natural or a list: no
    /// longer than it is deep.
    fn value(&self) -> Bounds {
        both(&self.long, &self.deep, true)
    }

    /// The same, kept to the range a summary holds and `depth` shapes deep:
    /// a lower bound only as a number.
    fn clamped(&self, depth: usize) -> Self {
        let kept = |bounds: &Bounds| -> Bounds {
            let kept = |bound: i64| (bound <= MOST_OFFSET).then(|| bound.max(LEAST_OFFSET));
            bounds.iter().map(|bound| bound.and_then(kept)).collect()
        };
        let least = self
            .least
            .first()
            .copied()
            .flatten()
            .map_or_else(Vec::new, |least| {
                let mut held = vec![None; self.least.len()];
                held[0] = Some(least.clamp(0, 2));
                held
            });
        Self {
            deep: kept(&self.deep),
            long: kept(&self.long),
            least,
            shape: match &self.shape {
                Shape::Known(_) if depth == 0 => Shape::Unknown,
                shape => shape.mapped(|field| field.clamped(depth - 1)),
            },
            ..Self::unknown()
        }
    }
}

/// The top of a measured gap: a natural parameter, or a number a body binds
/// before anything else, which is the same every time round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Top {
    Parameter(usize),
    Number { value: u64, local: usize },
}

/// The gaps `(top + 1) ∸ bottom` a round may close: between each two natural
/// parameters, and from each number a body first binds down to each. A
/// parameter every call hands one value is that value inside, once
/// optimized, and a guard then compares with the number.
fn gaps(program: &Program, id: FnId) -> Vec<(Top, usize)> {
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

/// Each definition's frame for one tier, made the first time it is asked.
#[derive(Default)]
struct Frames(RefCell<HashMap<FnId, Rc<Frame>>>);

impl Frames {
    fn of(&self, program: &Program, id: FnId, tier: &Tier<'_>) -> Rc<Frame> {
        Rc::clone(
            self.0
                .borrow_mut()
                .entry(id)
                .or_insert_with(|| Rc::new(Frame::of(program, id, tier))),
        )
    }
}

/// What reading answers takes: which definitions are a sequence operation,
/// answered by what it means rather than by its body; which call nothing
/// going round and are small enough to read in place at a call; which are
/// joins, and what every call of each join hands it; and the frames
/// summaries are kept in.
struct Answers {
    sequences: Vec<Option<SequenceOperation>>,
    simple: Vec<bool>,
    joins: Vec<bool>,
    entered: HashMap<FnId, Facts>,
    frames: Frames,
}

/// How many terms a definition read in place at a call may have, and how
/// deep such reading goes.
const MOST_READ_IN_PLACE: usize = 48;
const DEEPEST_IN_PLACE: usize = 3;

impl Answers {
    fn of(program: &Program, operations: &[Option<Operation>]) -> Self {
        let calls = graph(program);
        let mut simple = vec![false; calls.len()];
        for round in rounds(&calls) {
            let &[id] = round.as_slice() else {
                continue;
            };
            if let Some(body) = program.function(id).body() {
                simple[id.index()] =
                    !calls[id.index()].contains(&id) && terms(program, body) <= MOST_READ_IN_PLACE;
            }
        }
        let joins = (0..calls.len())
            .map(|at| join(program, FnId::at(at)))
            .collect();
        let mut answers = Self {
            sequences: super::arithmetic::recognise_sequences(program, operations),
            simple,
            joins,
            entered: HashMap::new(),
            frames: Frames::default(),
        };
        answers.enter(program, operations, &calls);
        answers
    }

    /// What every call of each join hands it, as facts between its
    /// parameters: what holds at each call, read in its caller, and of
    /// those, what holds at all of them.
    ///
    /// A match going on past an arm that may leave calls the rest of its
    /// body as a join, handing it what it holds: a list, say, and its rest
    /// taken apart, which the join would otherwise read as two lists of
    /// nothing to each other, so that what it answers, one or the other's
    /// remainder, is no longer than either. A join may call the next, so
    /// each is read once every definition calling it has been, knowing
    /// what they all handed it. Joins calling each other round are read
    /// last, knowing nothing of what they were handed, and what they hand
    /// on holds all the same.
    fn enter(&mut self, program: &Program, operations: &[Option<Operation>], calls: &[Vec<FnId>]) {
        let joined = self.joined(calls);
        let mut waiting = vec![0_usize; calls.len()];
        for to in joined.iter().flatten() {
            waiting[to.index()] += 1;
        }
        let mut ready: Vec<FnId> = (0..calls.len())
            .map(FnId::at)
            .filter(|id| !self.joins[id.index()] && !joined[id.index()].is_empty())
            .collect();
        let mut read = vec![false; calls.len()];
        let mut gathered: HashMap<FnId, Facts> = HashMap::new();
        while let Some(id) = ready.pop() {
            read[id.index()] = true;
            self.gather(program, operations, id, &mut gathered);
            for &to in &joined[id.index()] {
                waiting[to.index()] -= 1;
                if waiting[to.index()] > 0 {
                    continue;
                }
                if let Some(facts) = gathered.remove(&to) {
                    self.entered.insert(to, facts);
                }
                if !joined[to.index()].is_empty() {
                    ready.push(to);
                }
            }
        }
        let round: Vec<FnId> = (0..calls.len())
            .map(FnId::at)
            .filter(|id| !read[id.index()] && !joined[id.index()].is_empty())
            .collect();
        for &id in &round {
            self.gather(program, operations, id, &mut gathered);
        }
        self.entered.extend(gathered);
    }

    /// The joins each definition calls, each once.
    fn joined(&self, calls: &[Vec<FnId>]) -> Vec<Vec<FnId>> {
        calls
            .iter()
            .map(|called| {
                let mut joins: Vec<FnId> = called
                    .iter()
                    .copied()
                    .filter(|to| self.joins[to.index()])
                    .collect();
                joins.sort_unstable();
                joins.dedup();
                joins
            })
            .collect()
    }

    /// What each call `id` makes of a join hands it, kept with what other
    /// calls of that join handed it where all of them hold.
    fn gather(
        &self,
        program: &Program,
        operations: &[Option<Operation>],
        id: FnId,
        gathered: &mut HashMap<FnId, Facts>,
    ) {
        let (none, within) = (HashMap::new(), HashSet::new());
        let tier = Tier::summarised(&none, self);
        let mut reader = Reader::new(program, id, &within, operations, tier);
        reader.handed = Some(Vec::new());
        reader.answer();
        for (to, facts) in reader.handed.unwrap_or_default() {
            let held = gathered.entry(to).or_insert_with(|| facts.clone());
            *held = relations::join(held, &facts);
        }
    }
}

/// What a frontend names the definition a way no value takes calls.
///
/// Below a list split two ways, the list and its end are both taken apart, and
/// what one decides the other may test again, so a decision tree has ways
/// the clauses' coverage says nothing reaches. Barb has nothing answering
/// a type no value has but a call that never comes back, so the definition
/// goes round on itself. Only such a way calls it, and none is taken, so
/// it is never read for whether it stops. The comma keeps a written name
/// from being it.
pub const UNREACHED: &str = "unreachable, no value goes this way";

/// Whether a definition is the one [`UNREACHED`] names, answering a type
/// no value has.
fn unreached(program: &Program, id: FnId) -> bool {
    let function = program.function(id);
    program.name(function.name) == UNREACHED
        && super::type_shape(program, function.result) == super::TypeShape::Uninhabited
}

/// Whether a definition is a join: the rest of a body past a branch that
/// may leave, made a definition of its own, which only the body it was
/// made from calls. Its name says so, as a written name has no comma.
fn join(program: &Program, id: FnId) -> bool {
    program
        .name(program.function(id).name)
        .ends_with(", going on")
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

/// A round of calls nothing here shows stops.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unproved {
    /// The definitions in it, in the order they were written.
    pub functions: Vec<FnId>,
    /// Whether it reaches no external routine, so that whether it stops
    /// depends on nothing outside the program.
    pub pure: bool,
}

/// Every round of calls nothing here shows stops. A round of one that does
/// not call itself never goes round, and is never among them, nor is the
/// definition a way no value takes calls, [`UNREACHED`].
#[must_use]
pub fn unproved(program: &Program) -> Vec<Unproved> {
    let calls = graph(program);
    let pure = super::calls::pure(program, &program.recognition());
    let operations = super::arithmetic::recognise(program);
    let none = HashMap::new();
    let mut answered = None;
    let mut unproved = Vec::new();
    for (round, passing) in going_rounds(program, &calls) {
        // Gaps and what calls answer are read only for a round nothing
        // less shows stops: a gap is a measure for each two naturals.
        let (plain, gapped) = (Frames::default(), Frames::default());
        let shown = |gaps, frames| {
            descends(
                program,
                &round,
                &passing,
                &operations,
                Tier::showing(gaps, &none, None, frames),
            )
        };
        if shown(false, &plain) || shown(true, &gapped) {
            continue;
        }
        let (answers, summaries) = answered.get_or_insert_with(|| {
            let answers = Answers::of(program, &operations);
            let summaries = summaries_of(program, &operations, &answers);
            (answers, summaries)
        });
        let frames = Frames::default();
        let tier = Tier::showing(true, summaries, Some(answers), &frames);
        if !descends(program, &round, &passing, &operations, tier) {
            unproved.push(Unproved {
                pure: pure[round[0].index()],
                functions: round,
            });
        }
    }
    unproved
}

/// Each round of calls that may go round, beside which of it are read in
/// place where another of it calls them.
fn going_rounds(program: &Program, calls: &[Vec<FnId>]) -> Vec<(Vec<FnId>, HashSet<FnId>)> {
    let rounds = rounds(calls);
    let entered = entered_from_outside(calls, &rounds);
    rounds
        .into_iter()
        .filter(|round| goes_round(program, calls, round))
        .map(|round| {
            let passing = passing(program, calls, &entered, &round);
            (round, passing)
        })
        .collect()
}

/// Whether a round may go round at all: one definition on its own does only
/// where it calls itself, and what a way no value takes calls is never
/// called.
fn goes_round(program: &Program, calls: &[Vec<FnId>], round: &[FnId]) -> bool {
    let alone = round.len() == 1 && !calls[round[0].index()].contains(&round[0]);
    !alone && !round.iter().all(|&id| unreached(program, id))
}

/// The definitions of a round of more than one read in place where another
/// of it calls them: each small, calling itself nowhere, and called from
/// nowhere outside the round, so the round only passes through it. A
/// round is entered at the others, which are read for, and where none is
/// left, nothing is read in place.
fn passing(
    program: &Program,
    calls: &[Vec<FnId>],
    entered: &[bool],
    round: &[FnId],
) -> HashSet<FnId> {
    if round.len() < 2 {
        return HashSet::new();
    }
    let passing: HashSet<FnId> = round
        .iter()
        .copied()
        .filter(|&id| {
            let small = program
                .function(id)
                .body()
                .is_some_and(|body| terms(program, body) <= MOST_READ_IN_PLACE);
            small && !entered[id.index()] && !calls[id.index()].contains(&id)
        })
        .collect();
    if passing.len() == round.len() {
        return HashSet::new();
    }
    passing
}

/// Which definitions something outside their own round calls.
fn entered_from_outside(calls: &[Vec<FnId>], rounds: &[Vec<FnId>]) -> Vec<bool> {
    let mut round_of = vec![0; calls.len()];
    for (at, round) in rounds.iter().enumerate() {
        for id in round {
            round_of[id.index()] = at;
        }
    }
    let mut entered = vec![false; calls.len()];
    for (caller, called) in calls.iter().enumerate() {
        for callee in called {
            if round_of[callee.index()] != round_of[caller] {
                entered[callee.index()] = true;
            }
        }
    }
    entered
}

/// What each definition answers against its measures, as far as its body
/// shows: the greatest fixpoint, each round assumed to answer as little as
/// anything and weakened until what its bodies answer under the assumption
/// is what was assumed. What a call answers is only said of a call that
/// answers, which is all a proof of stopping reads it for: the facts of one
/// step round, where the rest has already come back.
fn summaries_of(
    program: &Program,
    operations: &[Option<Operation>],
    answers: &Answers,
) -> HashMap<FnId, Local> {
    let calls = graph(program);
    let mut summaries = HashMap::new();
    for round in rounds(&calls) {
        let bodied: Vec<FnId> = round
            .into_iter()
            .filter(|id| program.function(*id).body().is_some())
            .collect();
        for &id in &bodied {
            let tier = Tier::summarised(&summaries, answers);
            let keys = answers.frames.of(program, id, &tier).keys.len();
            summaries.insert(id, Local::smallest(keys));
        }
        let mut settled = false;
        for _ in 0..64 {
            let mut changed = false;
            for &id in &bodied {
                let tier = Tier::summarised(&summaries, answers);
                let answered = Reader::new(program, id, &HashSet::new(), operations, tier)
                    .answer()
                    .clamped(SHAPE_DEPTH);
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

/// How much a round is read for: plainly; with the gaps between its
/// naturals besides; and with what its calls answer besides that, which a
/// summary is worked out with too.
#[derive(Clone, Copy)]
struct Tier<'a> {
    /// Whether the gaps between naturals are measured.
    gaps: bool,
    /// Whether stopping is being shown here, so graphs are built, fields
    /// measured and small calls read in place; or a summary worked out.
    showing: bool,
    summaries: &'a HashMap<FnId, Local>,
    answers: Option<&'a Answers>,
    frames: &'a Frames,
}

impl<'a> Tier<'a> {
    const fn showing(
        gaps: bool,
        summaries: &'a HashMap<FnId, Local>,
        answers: Option<&'a Answers>,
        frames: &'a Frames,
    ) -> Self {
        Self {
            gaps,
            showing: true,
            summaries,
            answers,
            frames,
        }
    }

    const fn summarised(summaries: &'a HashMap<FnId, Local>, answers: &'a Answers) -> Self {
        Self {
            gaps: false,
            showing: false,
            summaries,
            answers: Some(answers),
            frames: &answers.frames,
        }
    }
}

/// An operand of a recognized operation, as far as telling two alike goes:
/// whose value it is, or the number it is.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Operand {
    Local(usize),
    Number(u64),
}

/// What one definition's body says of the sizes it hands on: a graph per
/// call it makes to one it goes round with, beside that call, and what it
/// answers.
struct Reader<'a> {
    program: &'a Program,
    /// The definition read for: whose measures and gaps a graph's rows are,
    /// and whose call a graph begins at. A body read in place is read for
    /// the definition calling it.
    from: FnId,
    within: &'a HashSet<FnId>,
    /// The definitions of the round read in place where one of them calls
    /// another, rather than read as a graph.
    passing: Option<&'a HashSet<FnId>>,
    operations: &'a [Option<Operation>],
    tier: Tier<'a>,
    frame: Rc<Frame>,
    /// For each parameter here, the parameter of the definition whose
    /// frame this is that it is, where it is one: a body read in place is
    /// handed what its caller holds, and only a parameter there has its
    /// fields measured.
    params: Vec<Option<usize>>,
    /// How many calls deep in others this body is read in place.
    depth: usize,
    locals: Vec<Local>,
    held: Vec<(Graph, ExprId)>,
    /// Each local an arm learned more of, as it was before, so leaving the
    /// arm puts it back.
    journal: Vec<(usize, Local)>,
    /// Each recognized operation already worked out in scope, by what it
    /// was handed, and the local holding it: working one out again is the
    /// same value, so what a guard said of the first holds of the second.
    computed: Vec<(FnId, Vec<Operand>, usize)>,
    /// Each take worked out in scope, by what it was handed, and the local
    /// holding it, so a drop by the same count of the same list is known
    /// to be the rest of it.
    taken: Vec<(Vec<Operand>, usize)>,
    /// What each call of a join hands it, where that is being read.
    handed: Option<Vec<(FnId, Facts)>>,
    /// Where this is a body of the round read in place, what the definition
    /// it is read for held where it called it, which that definition's
    /// gaps are between.
    entry: Option<Rc<[Local]>>,
}

impl<'a> Reader<'a> {
    /// A parameter is itself: as deep as it is, and as long. A join's
    /// parameters stand as every call of it hands them.
    fn new(
        program: &'a Program,
        from: FnId,
        within: &'a HashSet<FnId>,
        operations: &'a [Option<Operation>],
        tier: Tier<'a>,
    ) -> Self {
        let frame = tier.frames.of(program, from, &tier);
        let params = program.params(from).len();
        let locals = (0..params)
            .map(|at| {
                let length = frame.length(at);
                Local {
                    deep: frame.itself(at, true),
                    long: length.map_or_else(Vec::new, |length| frame.itself(length, true)),
                    least: length.map_or_else(Vec::new, |length| frame.itself(length, false)),
                    same: Some(at),
                    ..Local::unknown()
                }
            })
            .collect();
        let mut reader = Self {
            program,
            from,
            within,
            passing: None,
            operations,
            tier,
            frame,
            params: (0..params).map(Some).collect(),
            depth: 0,
            locals,
            held: Vec::new(),
            journal: Vec::new(),
            computed: Vec::new(),
            taken: Vec::new(),
            handed: None,
            entry: None,
        };
        if let Some(entered) = tier.answers.and_then(|answers| answers.entered.get(&from)) {
            reader.assume(entered);
        }
        reader
    }

    /// What the body answers, reading it whole.
    fn answer(&mut self) -> Local {
        let body = self
            .program
            .function(self.from)
            .body()
            .expect("a definition read has a body");
        self.read(body)
    }

    /// Each binding takes the next level. What the body answers.
    fn read(&mut self, body: Body) -> Local {
        for &binding in self.program.bindings(body.bindings) {
            let mut local = self.term(binding);
            local.same.get_or_insert(self.locals.len());
            self.locals.push(local);
        }
        self.term(body.tail)
    }

    fn term(&mut self, id: ExprId) -> Local {
        match self.program.expr(id) {
            Expr::Atom(atom) => self.locals[atom.0.index()].clone(),
            Expr::Static(value) => self.constant(value),
            Expr::Con(ctor, args) => self.built(ctor, self.program.atoms(args)),
            Expr::Call(to, args) => self.call(id, to, self.program.atoms(args)),
            Expr::Match(scrutinee, arms) => {
                let verdict = self.matched(id);
                let answered = self.arms(scrutinee, arms).unwrap_or_else(Local::unknown);
                Local {
                    verdict,
                    ..answered
                }
            }
        }
    }

    /// A value known outright: its constructor, whatever its fields are,
    /// and as long as it is where it is a list or a natural.
    fn constant(&self, value: super::ConstId) -> Local {
        let constant = self.program.constant(value);
        let ctor = constant.constructor();
        let fields = vec![Local::unknown(); self.program.fields(ctor).len()];
        let shape = Shape::Known(Rc::new(vec![(ctor, fields)]));
        let (size, natural) = match constant.view() {
            ConstantView::Spine(spine) => (i64::try_from(spine.length()).ok(), false),
            ConstantView::Natural(natural) => {
                let size = natural
                    .try_u64()
                    .ok()
                    .and_then(|size| i64::try_from(size).ok());
                (size, true)
            }
            ConstantView::Constructor(_) => (None, false),
        };
        let Some(size) = size else {
            // A constructor of nothing is as small as a value is.
            let deep = if self.program.fields(ctor).is_empty() {
                self.frame.most(0)
            } else {
                Vec::new()
            };
            return Local {
                deep,
                shape,
                ..Local::unknown()
            };
        };
        let long = self.frame.most(size);
        Local {
            deep: if natural { long.clone() } else { Vec::new() },
            long,
            least: self.frame.least(size),
            shape,
            ..Local::unknown()
        }
    }

    /// A constructor is one deeper than its deepest field, a spine's push
    /// one longer than its rest, and a list wrapped as long as the list.
    fn built(&self, ctor: super::CtorId, args: &[Atom]) -> Local {
        let fields = args.iter().map(|arg| &self.locals[arg.0.index()]);
        // A constructor of nothing is as small as a value is.
        let deep = fields
            .clone()
            .map(|field| field.deep.clone())
            .reduce(|a, b| either(&a, &b, true))
            .map_or_else(|| self.frame.most(0), |deepest| shifted(&deepest, 1));
        let shape = Shape::Known(Rc::new(vec![(
            ctor,
            fields.map(|field| field.clamped(SHAPE_DEPTH - 1)).collect(),
        )]));
        let (long, least) = match super::shape(self.program, self.program.ctor(ctor).owner) {
            super::Shape::Spine { nil, .. } if nil == ctor => {
                (self.frame.most(0), self.frame.least(0))
            }
            super::Shape::Spine { recursive, .. } => args.get(recursive).map_or_else(
                || (Vec::new(), Vec::new()),
                |rest| {
                    let rest = &self.locals[rest.0.index()];
                    (shifted(&rest.long, 1), shifted(&rest.least, 1))
                },
            ),
            super::Shape::Tagged => match args {
                [list] if wraps_list(self.program, self.program.ctor(ctor).owner) => {
                    let list = &self.locals[list.0.index()];
                    (list.long.clone(), list.least.clone())
                }
                _ => (Vec::new(), Vec::new()),
            },
        };
        Local {
            deep,
            long,
            least,
            shape,
            ..Local::unknown()
        }
    }

    /// A call: a graph where it goes round, or what goes round in its body
    /// where that is read in place, and what it answers.
    fn call(&mut self, id: ExprId, to: FnId, args: &[Atom]) -> Local {
        let mut through = None;
        if self.within.contains(&to) {
            through = self.through(id, to, args);
            if through.is_none() {
                let graph = self.matrix(to, args);
                self.held.push((graph, id));
            }
        }
        let joined = self
            .tier
            .answers
            .is_some_and(|answers| answers.joins[to.index()]);
        if joined && self.handed.is_some() {
            let facts = self.handing(args);
            self.handed.get_or_insert_default().push((to, facts));
        }
        let mut result = match self.operations[to.index()] {
            // Worked out again, it is what was worked out before, and what
            // a guard learned of that holds of it.
            Some(operation) => match self.recomputed(to, args) {
                Some(before) => Local {
                    same: Some(before),
                    ..self.arithmetic(operation, args).meet(&self.locals[before])
                },
                None => self.arithmetic(operation, args),
            },
            None => self.defined(to, args, through),
        };
        let values = self.values(args);
        if let Value::Verdict(verdict) =
            relations::called(self.program, self.operations, to, &values)
        {
            result.verdict = Some(verdict);
        }
        result
    }

    /// What a call of a definition, not an operation, answers: what its body
    /// read in place says, where it is, besides what `answered` does; and
    /// where it is a drop past a take, which.
    fn defined(&mut self, to: FnId, args: &[Atom], through: Option<Local>) -> Local {
        let answered = self.answered(to, args);
        let answered = match through {
            Some(read) => read.meet(&answered),
            None => answered,
        };
        Local {
            past: self.split(to, args),
            ..answered
        }
    }

    /// How what a call hands stand against each other, by their bounds
    /// here: for each two arguments, which is no longer, or shorter, where
    /// one is.
    fn handing(&self, args: &[Atom]) -> Facts {
        let mut facts = Vec::new();
        for (left, first) in args.iter().enumerate() {
            for (right, second) in args.iter().enumerate().skip(left + 1) {
                let first = &self.locals[first.0.index()];
                let second = &self.locals[second.0.index()];
                let over = excess(first, second);
                let under = excess(second, first);
                if let Some(rel) = relations::standing(over, under) {
                    facts.push(relations::Fact { left, right, rel });
                }
            }
        }
        facts
    }

    /// The local already holding what a recognized operation works out of
    /// these operands, where one does; otherwise this one is noted as the
    /// next local, which it becomes where it is bound.
    fn recomputed(&mut self, to: FnId, args: &[Atom]) -> Option<usize> {
        let operands = self.operands(args);
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

    /// What each argument is, as far as telling two alike goes.
    fn operands(&self, args: &[Atom]) -> Vec<Operand> {
        args.iter()
            .map(|arg| {
                let at = arg.0.index();
                self.exact(at)
                    .map_or_else(|| Operand::Local(self.same(at)), Operand::Number)
            })
            .collect()
    }

    /// A take is noted as the next local, which it becomes where it is
    /// bound; a drop by the same count of the same list is what is past
    /// it.
    fn split(&mut self, to: FnId, args: &[Atom]) -> Option<Split> {
        let operation = (*self.tier.answers?.sequences.get(to.index())?)?;
        let operands = self.operands(args);
        match operation {
            SequenceOperation::Take => {
                self.taken.push((operands, self.locals.len()));
                None
            }
            SequenceOperation::Drop => {
                self.taken
                    .iter()
                    .find(|(taken, _)| *taken == operands)
                    .map(|&(_, front)| Split {
                        front,
                        whole: args[0].0.index(),
                    })
            }
            _ => None,
        }
    }

    /// What a call answers: what its summary says with what was handed,
    /// and besides that what a sequence operation means, or what its body
    /// says read in place.
    fn answered(&self, to: FnId, args: &[Atom]) -> Local {
        let summarised = self
            .tier
            .answers
            .zip(self.tier.summaries.get(&to))
            .map_or_else(Local::unknown, |(answers, summary)| {
                let tier = Tier::summarised(self.tier.summaries, answers);
                let theirs = answers.frames.of(self.program, to, &tier);
                let handed: Vec<_> = theirs
                    .measures
                    .iter()
                    .map(|&measure| self.frame.tightest(&self.quantity(measure, args)))
                    .collect();
                self.instantiated(summary, &theirs, &handed)
            });
        match self
            .sequence(to, args)
            .or_else(|| self.read_in_place(to, args))
        {
            Some(read) => read.meet(&summarised),
            None => summarised,
        }
    }

    /// A callee's summary read here: each of its measures replaced by what
    /// was handed for it, field by field of the shape it answers.
    fn instantiated(&self, summary: &Local, theirs: &Frame, handed: &[Vec<(u64, i64)>]) -> Local {
        let least = summary.least.first().copied().flatten();
        Local {
            deep: self.frame.substituted(theirs, &summary.deep, handed),
            long: self.frame.substituted(theirs, &summary.long, handed),
            least: least.map_or_else(Vec::new, |least| self.frame.least(least)),
            shape: summary
                .shape
                .mapped(|field| self.instantiated(field, theirs, handed)),
            ..Local::unknown()
        }
    }

    /// What bounds a callee's measure of what it is handed, against this
    /// definition's measures.
    fn quantity(&self, measure: Measure, args: &[Atom]) -> Bounds {
        let arg = |at: usize| &self.locals[args[at].0.index()];
        match measure {
            Measure::Depth(at) => arg(at).deep.clone(),
            Measure::Length(at) => arg(at).value(),
            Measure::Field { param, ctor, field } => match &arg(param).shape {
                Shape::Known(entries) => entries
                    .iter()
                    .find(|(held, _)| *held == ctor)
                    .and_then(|(_, fields)| fields.get(field))
                    .map_or_else(Vec::new, |field| field.deep.clone()),
                Shape::Unknown | Shape::Least => Vec::new(),
            },
        }
    }

    /// What a sequence operation answers, by what it means: how many a
    /// list holds is as long as it, its first `n` are no longer than it or
    /// than `n`, and it without some of its first, where there are some to
    /// take, is shorter than it. Where the count is not known, what is
    /// dropped may be everything.
    fn sequence(&self, to: FnId, args: &[Atom]) -> Option<Local> {
        let operation = (*self.tier.answers?.sequences.get(to.index())?)?;
        let list_at = args.first()?.0.index();
        let list = &self.locals[list_at];
        let least = |least: i64| self.frame.least(least.max(0));
        match operation {
            SequenceOperation::Length => Some(Local {
                deep: list.value(),
                long: list.value(),
                least: least(self.minimum(list_at)),
                ..Local::unknown()
            }),
            SequenceOperation::Take => {
                let count = args.get(1)?.0.index();
                Some(Local {
                    deep: list.deep.clone(),
                    long: both(&list.value(), &self.locals[count].value(), true),
                    least: least(self.minimum(list_at).min(self.minimum(count))),
                    ..Local::unknown()
                })
            }
            SequenceOperation::Drop => {
                let count = args.get(1)?.0.index();
                let strict = i64::from(self.minimum(count) >= 1 && self.minimum(list_at) >= 1);
                let dropped = self
                    .exact(count)
                    .and_then(|exact| i64::try_from(exact).ok());
                Some(Local {
                    deep: shifted(&list.deep, -strict),
                    long: shifted(&list.value(), -strict),
                    least: least(dropped.map_or(0, |dropped| self.minimum(list_at) - dropped)),
                    ..Local::unknown()
                })
            }
            SequenceOperation::ReverseOnto
            | SequenceOperation::Prepend
            | SequenceOperation::Append
            | SequenceOperation::Replace => self.rebuilt(operation, args),
        }
    }

    /// How long a list built of others is: one put before another, either
    /// way round, as long as both; with one more element, one longer; and
    /// with an element written over, as long as it was. How deep it is
    /// depends on how deep each element is and where it lies, so only its
    /// length is said.
    fn rebuilt(&self, operation: SequenceOperation, args: &[Atom]) -> Option<Local> {
        let list_at = args.first()?.0.index();
        let list = &self.locals[list_at];
        let (long, least) = match operation {
            SequenceOperation::ReverseOnto | SequenceOperation::Prepend => {
                let onto = &self.locals[args.get(1)?.0.index()];
                let long = self.frame.summed(&list.value(), &onto.value());
                (long, self.grown(Operation::Add, &args[..2]))
            }
            SequenceOperation::Append => {
                (shifted(&list.value(), 1), shifted(&self.floor(list_at), 1))
            }
            SequenceOperation::Replace => (list.value(), self.floor(list_at)),
            SequenceOperation::Length | SequenceOperation::Take | SequenceOperation::Drop => {
                return None;
            }
        };
        Some(Local {
            long,
            least,
            ..Local::unknown()
        })
    }

    /// What a call of a definition of the round answers, where its body is
    /// read in place: one that does not call itself, a few calls deep. What
    /// goes round in it is read as going round from here, with what its
    /// arguments are here, so `left` known above nought where a write
    /// loop's first half calls its second is known where the second
    /// subtracts what was written from it. A path through it is still a
    /// path, so whether every one descends is unchanged.
    fn through(&mut self, id: ExprId, to: FnId, args: &[Atom]) -> Option<Local> {
        if !self.passing?.contains(&to) || to == self.from || self.depth >= DEEPEST_IN_PLACE {
            return None;
        }
        let body = self.program.function(to).body()?;
        let mut inner = self.inner(args);
        inner.entry = Some(self.entry.clone().unwrap_or_else(|| self.entered_prefix()));
        let answer = inner.read(body);
        // Each way round begins at this call, whichever call in the body
        // read here goes on.
        self.held
            .extend(inner.held.into_iter().map(|(graph, _)| (graph, id)));
        Some(Local {
            same: None,
            verdict: None,
            rest_of: None,
            past: None,
            given: Self::handed_lengths(&answer.given, args),
            ..answer
        })
    }

    /// What this definition holds that its gaps are between: its
    /// parameters, and the numbers it has bound so far.
    fn entered_prefix(&self) -> Rc<[Local]> {
        let needed = self
            .frame
            .gaps
            .iter()
            .map(|&(top, bottom)| match top {
                Top::Parameter(at) => at.max(bottom) + 1,
                Top::Number { local, .. } => local.max(bottom) + 1,
            })
            .max()
            .unwrap_or(0)
            .min(self.locals.len());
        Rc::from(&self.locals[..needed])
    }

    /// What this definition held where the body read began: its own locals,
    /// or, for a body of the round read in place, its caller's.
    fn entered(&self) -> &[Local] {
        self.entry.as_deref().unwrap_or(&self.locals)
    }

    /// What a call of a definition going round nowhere answers, its body
    /// read here with what its arguments are here. Only where stopping is
    /// being shown: working out what every definition answers, round after
    /// round, would read each callee again every time.
    fn read_in_place(&self, to: FnId, args: &[Atom]) -> Option<Local> {
        let answers = self.tier.answers?;
        if !self.tier.showing && self.depth == 0
            || self.depth >= DEEPEST_IN_PLACE
            || !answers.simple.get(to.index()).copied().unwrap_or(false)
            || self.within.contains(&to)
        {
            return None;
        }
        let body = self.program.function(to).body()?;
        let mut inner = self.inner(args);
        let answer = inner.read(body);
        debug_assert!(inner.held.is_empty(), "nothing read in place goes round");
        // Whose value it is, and what its verdict says, are of locals there.
        Some(Local {
            same: None,
            verdict: None,
            rest_of: None,
            past: None,
            given: Self::handed_lengths(&answer.given, args),
            ..answer
        })
    }

    /// A reader of a body called here, read for the definition read here:
    /// its parameters are what was handed, against the measures here. What a verdict handed says
    /// is said there of the parameters it was handed as, and of nothing
    /// else: the locals here are not the locals there.
    fn inner(&self, args: &[Atom]) -> Self {
        let handed: Vec<usize> = args.iter().map(|arg| self.same(arg.0.index())).collect();
        let locals = args
            .iter()
            .enumerate()
            .map(|(at, arg)| {
                let local = &self.locals[arg.0.index()];
                Local {
                    same: Some(at),
                    rest_of: None,
                    past: None,
                    given: Vec::new(),
                    verdict: local
                        .verdict
                        .as_ref()
                        .map(|verdict| relations::renamed(verdict, &handed)),
                    ..local.clone()
                }
            })
            .collect();
        Reader {
            program: self.program,
            from: self.from,
            within: self.within,
            passing: self.passing,
            operations: self.operations,
            tier: self.tier,
            frame: Rc::clone(&self.frame),
            params: args
                .iter()
                .map(|arg| self.parameter(arg.0.index()))
                .collect(),
            depth: self.depth + 1,
            locals,
            held: Vec::new(),
            journal: Vec::new(),
            computed: Vec::new(),
            taken: Vec::new(),
            handed: None,
            entry: None,
        }
    }

    /// What a match answers, which is a verdict where its arms answer them.
    fn matched(&self, id: ExprId) -> Option<Verdict> {
        let mut env: Vec<Value> = (0..self.locals.len()).map(|at| self.value(at)).collect();
        match relations::evaluated(self.program, self.operations, id, &mut env) {
            Value::Verdict(verdict) => Some(verdict),
            Value::Size(_) | Value::Unknown => None,
        }
    }

    /// Each arm read under what its constructor says of the scrutinee, and
    /// an arm the scrutinee's verdict or shape cannot reach not read at all.
    /// What the arms answer, whichever answered.
    fn arms(&mut self, scrutinee: Atom, arms: super::Range) -> Option<Local> {
        let at = scrutinee.0.index();
        let mut answered: Option<Local> = None;
        for arm in self.program.arms(arms) {
            let Some((shaped, given)) = self.reached(at, arm.ctor) else {
                continue;
            };
            let (level, mark) = (self.locals.len(), self.journal.len());
            self.bind_fields(at, arm.ctor, shaped.as_deref());
            self.assume(&given);
            let lengths = self.locals[at].lengths(arm.ctor).cloned();
            for (local, least) in lengths.into_iter().flatten() {
                if local < level {
                    self.lengthen(local, least);
                }
            }
            let mut arm_answer = self.read(arm.body);
            self.note_lengths(&mut arm_answer, level);
            self.locals.truncate(level);
            self.computed.retain(|&(_, _, at)| at < level);
            self.taken.retain(|&(_, at)| at < level);
            while self.journal.len() > mark {
                let (at, before) = self.journal.pop().expect("a change to put back");
                if at < level {
                    self.locals[at] = before;
                }
            }
            answered = Some(match answered {
                None => arm_answer,
                Some(before) => before.join(&arm_answer),
            });
        }
        answered
    }

    /// What an arm's answer being each constructor says of how long this
    /// body's parameters are, where it is read in place: as long as they
    /// are known to be here. What it says of a local the arm bound is out
    /// of scope once the arm is left.
    fn note_lengths(&self, answer: &mut Local, level: usize) {
        for (_, lengths) in &mut answer.given {
            lengths.retain(|&(at, _)| at < level);
        }
        answer.given.retain(|(_, lengths)| !lengths.is_empty());
        let Shape::Known(entries) = &answer.shape else {
            return;
        };
        if self.depth == 0 {
            return;
        }
        let known: Lengths = (0..self.params.len())
            .map(|at| (at, self.minimum(at)))
            .filter(|&(_, least)| least >= 1)
            .collect();
        if known.is_empty() {
            return;
        }
        for &(ctor, _) in entries.iter() {
            match answer.given.iter_mut().find(|(held, _)| *held == ctor) {
                Some((_, lengths)) => {
                    for &(at, least) in &known {
                        match lengths.iter_mut().find(|(held, _)| *held == at) {
                            Some((_, held)) => *held = (*held).max(least),
                            None => lengths.push((at, least)),
                        }
                    }
                }
                None => answer.given.push((ctor, known.clone())),
            }
        }
    }

    /// What a body read in place says of how long what it was handed is,
    /// said of the locals here it was handed.
    fn handed_lengths(
        given: &[(super::CtorId, Lengths)],
        args: &[Atom],
    ) -> Vec<(super::CtorId, Lengths)> {
        given
            .iter()
            .filter_map(|(ctor, lengths)| {
                let lengths: Lengths = lengths
                    .iter()
                    .filter_map(|&(at, least)| Some((args.get(at)?.0.index(), least)))
                    .collect();
                (!lengths.is_empty()).then_some((*ctor, lengths))
            })
            .collect()
    }

    /// Whether an arm for `ctor` can be reached from what local `at` is,
    /// and if so, what its shape says of the fields and its verdict of the
    /// sizes around.
    fn reached(&self, at: usize, ctor: super::CtorId) -> Option<(Option<Vec<Local>>, Facts)> {
        let count = self.program.fields(ctor).len();
        let shaped = match &self.locals[at].shape {
            Shape::Unknown => None,
            Shape::Least => Some(vec![Local::smallest(self.frame.keys.len()); count]),
            Shape::Known(entries) => Some(
                entries
                    .iter()
                    .find(|(held, _)| *held == ctor)
                    .map(|(_, fields)| fields.clone())?,
            ),
        };
        let given = match &self.locals[at].verdict {
            Some(verdict) => {
                let tag = usize::try_from(self.program.tag(ctor)).expect("a tag fits");
                verdict.outcomes[tag].clone()?
            }
            _ => Vec::new(),
        };
        Some((shaped, given))
    }

    /// The fields an arm for `ctor` binds of local `at`: one constructor
    /// shallower than it, the rest of a spine one shorter, a wrapped list
    /// as long as its wrapper, what its shape says besides, and a field of
    /// a parameter measured as itself.
    fn bind_fields(&mut self, at: usize, ctor: super::CtorId, shaped: Option<&[Local]>) {
        let level = self.locals.len();
        let rest = match super::shape(self.program, self.program.ctor(ctor).owner) {
            super::Shape::Spine {
                cons, recursive, ..
            } if cons == ctor => Some(recursive),
            _ => None,
        };
        if rest.is_some() {
            self.lengthen(at, 1);
        }
        let wrapped = wraps_list(self.program, self.program.ctor(ctor).owner);
        let scrutinee = &self.locals[at];
        let param = self.parameter(at);
        let mut fields = Vec::new();
        for field in 0..self.program.fields(ctor).len() {
            let is_rest = rest == Some(field);
            let (long, least) = if is_rest {
                (shifted(&scrutinee.long, -1), shifted(&scrutinee.least, -1))
            } else if wrapped {
                (scrutinee.long.clone(), scrutinee.least.clone())
            } else {
                (Vec::new(), Vec::new())
            };
            let mut local = Local {
                deep: shifted(&scrutinee.deep, -1),
                long,
                least,
                same: Some(level + field),
                rest_of: is_rest.then_some(at),
                ..Local::unknown()
            };
            if let Some(measure) = param.and_then(|param| self.frame.field(param, ctor, field)) {
                local.deep = both(&local.deep, &self.frame.itself(measure, true), true);
            }
            if let Some(shaped) = shaped.and_then(|fields| fields.get(field)) {
                local = local.meet(shaped);
            }
            fields.push(local);
        }
        self.locals.extend(fields);
    }

    /// The parameter of the definition whose frame this is that local `at`
    /// is, where it is one.
    fn parameter(&self, at: usize) -> Option<usize> {
        let same = self.locals[at].same?;
        self.params.get(same).copied().flatten()
    }

    /// Local `at`, noted in the journal so the arm learning something of it
    /// puts it back.
    fn change(&mut self, at: usize) -> &mut Local {
        self.journal.push((at, self.locals[at].clone()));
        &mut self.locals[at]
    }

    /// Local `at` known at least `least` long, and each list it is the
    /// rest of one longer than that. Where it is what is past a take, the
    /// list is at least as long, and the take shorter than it by `least`.
    fn lengthen(&mut self, at: usize, least: i64) {
        let mut at = at;
        let mut least = least;
        while self.locals[at].least.first().copied().flatten() < Some(least) {
            let keys = self.frame.keys.len();
            let local = self.change(at);
            if local.least.is_empty() {
                local.least = vec![None; keys];
            }
            local.least[0] = Some(least);
            let (rest_of, past) = (local.rest_of, local.past);
            if let Some(whole) = rest_of {
                at = whole;
                least = least.saturating_add(1);
            } else if let Some(Split { front, whole }) = past {
                let ceiling = shifted(&self.locals[whole].value(), -least);
                let taken = self.change(front);
                taken.long = both(&taken.long, &ceiling, true);
                at = whole;
            } else {
                return;
            }
        }
    }

    /// What a guard says, as bounds: where one side is at most the other,
    /// it is no larger than the other's upper bounds, and the other no
    /// smaller than its lower bounds; one more apart where it is less.
    /// Where the two differ and one is already known no larger, it is
    /// less: past `n == 0` being false, a natural is at least one.
    fn assume(&mut self, facts: &[relations::Fact]) {
        // A verdict may speak of what a match it came out of bound inside,
        // which is out of scope here.
        let known = self.locals.len();
        for fact in facts
            .iter()
            .filter(|fact| fact.left < known && fact.right < known)
        {
            let mut rel = fact.rel;
            if rel == LESS | GREATER {
                if self.no_larger(fact.left, fact.right) {
                    rel = LESS;
                } else if self.no_larger(fact.right, fact.left) {
                    rel = GREATER;
                }
            }
            let strict = i64::from(rel & EQUAL == 0);
            if rel & GREATER == 0 {
                self.at_most(fact.left, fact.right, strict);
            }
            if rel & LESS == 0 {
                self.at_most(fact.right, fact.left, strict);
            }
        }
    }

    /// Whether whatever is `x` is known no larger than whatever is `y`: as
    /// large as `x` may be, `y` is at least.
    fn no_larger(&self, x: usize, y: usize) -> bool {
        let floor = Local {
            least: self.floor(y),
            ..Local::unknown()
        };
        excess(&self.locals[x], &floor).is_some_and(|by| by <= 0)
    }

    /// Whatever is `x` at most whatever is `y`, less `by`.
    fn at_most(&mut self, x: usize, y: usize, by: i64) {
        let ceiling = shifted(&self.locals[y].value(), -by);
        let floor = shifted(&self.floor(x), by);
        for at in 0..self.locals.len() {
            let same = self.same(at);
            if same == x {
                let local = self.change(at);
                local.long = both(&local.long, &ceiling, true);
            }
            if same == y {
                let local = self.change(at);
                local.least = both(&local.least, &floor, false);
            }
        }
    }

    /// The lower bounds of a local, none of which is below nought.
    fn floor(&self, at: usize) -> Bounds {
        let mut least = self.locals[at].least.clone();
        if least.is_empty() {
            least = vec![None; self.frame.keys.len()];
        }
        least[0] = Some(self.minimum(at));
        least
    }

    /// Whose value a local is.    /// Whose value a local is.
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

    /// The natural a local is, where it is known outright.
    fn exact(&self, at: usize) -> Option<u64> {
        exact(&self.locals[at])
    }

    /// The least a local is, and never below nought.
    fn minimum(&self, at: usize) -> i64 {
        self.locals[at]
            .least
            .first()
            .copied()
            .flatten()
            .unwrap_or(0)
            .max(0)
    }

    /// What recognized natural arithmetic answers, by what its equations
    /// mean: a difference, a quotient and a remainder no larger than what
    /// they came from and smaller where they are strictly so, a sum the two
    /// added, a product at least a side, and a power above its exponent.
    fn arithmetic(&self, operation: Operation, args: &[Atom]) -> Local {
        let argument = |at: usize| &self.locals[args[at].0.index()];
        let minimum = |at: usize| self.minimum(args[at].0.index());
        let candidates: &[(&Local, bool)] = match operation {
            Operation::Monus => &[(argument(0), minimum(0) > 0 && minimum(1) > 0)],
            Operation::Div => &[(argument(0), minimum(0) > 0 && minimum(1) >= 2)],
            Operation::Mod => &[(argument(0), false), (argument(1), minimum(1) > 0)],
            Operation::And => &[(argument(0), false), (argument(1), false)],
            Operation::Add | Operation::Mul | Operation::Pow => &[],
            Operation::Or
            | Operation::Xor
            | Operation::Equals { .. }
            | Operation::LessThan { .. } => return Local::unknown(),
        };
        let mut long = if operation == Operation::Add {
            self.frame
                .summed(&argument(0).value(), &argument(1).value())
        } else {
            Vec::new()
        };
        for (argument, strict) in candidates {
            long = both(
                &long,
                &shifted(&argument.value(), -i64::from(*strict)),
                true,
            );
        }
        let least = match operation {
            Operation::Add | Operation::Mul => self.grown(operation, args),
            Operation::Div => self.halved(args),
            Operation::Pow => self.powered(args),
            _ => Vec::new(),
        };
        Local {
            deep: long.clone(),
            long,
            least,
            ..Local::unknown()
        }
    }

    /// A power of at least one is at least one, and of at least two, more
    /// than its exponent: `2^e` is at least `e + 1`, so past `n >= 2^e`,
    /// `e` is below `n`.
    fn powered(&self, args: &[Atom]) -> Bounds {
        let (base, exponent) = (args[0].0.index(), args[1].0.index());
        match self.minimum(base) {
            0 => Vec::new(),
            1 => self.frame.least(1),
            _ => shifted(&self.floor(exponent), 1),
        }
    }

    /// A quotient by a known number is at least the least dividend divided
    /// by it: halving something at least two is at least one.
    fn halved(&self, args: &[Atom]) -> Bounds {
        let Some(divisor) = self.exact(args[1].0.index()).filter(|&divisor| divisor > 0) else {
            return Vec::new();
        };
        let dividend = u64::try_from(self.minimum(args[0].0.index())).unwrap_or(0);
        self.frame
            .least(i64::try_from(dividend / divisor).unwrap_or(0))
    }

    /// How far a sum or a product is above what it came from: a sum at
    /// least either side and the other's least, and a product at least a
    /// side whose other is no less than one, and more than a side at least
    /// one whose other is at least two.
    fn grown(&self, operation: Operation, args: &[Atom]) -> Bounds {
        let (left, right) = (args[0].0.index(), args[1].0.index());
        let from = |side: usize, other: usize| -> Bounds {
            let by = match operation {
                Operation::Add => Some(self.minimum(other)),
                _ if self.minimum(other) >= 2 && self.minimum(side) >= 1 => Some(1),
                _ => (self.minimum(other) >= 1).then_some(0),
            };
            let floor = self.floor(side);
            match by {
                Some(by) if operation == Operation::Add => shifted(&floor, by),
                Some(by) => {
                    let mut grown = shifted(&floor, by);
                    grown[0] = Some(self.minimum(side).saturating_mul(self.minimum(other)));
                    grown
                }
                None => Vec::new(),
            }
        };
        both(&from(left, right), &from(right, left), false)
    }

    /// What one call hands on: for each of the callee's measures, how what
    /// it is handed stands against each measure here; and for each of its
    /// gaps, against each gap here.
    fn matrix(&self, to: FnId, args: &[Atom]) -> Graph {
        let theirs = self.tier.frames.of(self.program, to, &self.tier);
        let (ours_n, theirs_n) = (self.frame.measures.len(), theirs.measures.len());
        let rows = ours_n + self.frame.gaps.len();
        let columns = theirs_n + theirs.gaps.len();
        let mut cells = vec![Step::Unknown; rows * columns];
        for (column, &measure) in theirs.measures.iter().enumerate() {
            let handed = self.quantity(measure, args);
            if handed.is_empty() {
                continue;
            }
            for row in 0..ours_n {
                cells[row * columns + column] = step(handed[self.frame.single(row)]);
            }
        }
        for (row, &(top, bottom)) in self.frame.gaps.iter().enumerate() {
            for (column, &(handed, under)) in theirs.gaps.iter().enumerate() {
                let handed = match handed {
                    Top::Parameter(at) => Top::Parameter(args[at].0.index()),
                    number @ Top::Number { .. } => number,
                };
                cells[(ours_n + row) * columns + theirs_n + column] =
                    self.closes((top, bottom), (handed, args[under].0.index()));
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

    /// What the gap `(upper + 1) ∸ lower` handed on is against this
    /// definition's gap `(top + 1) ∸ bottom`: no wider where the handed pair
    /// lies within the old, narrower where besides it moved in and either
    /// pair is in order, its bottom no larger than its top, so the old gap
    /// was not nought. A handed top is a local here where it is a
    /// parameter's argument, and a number where it is the callee's own.
    fn closes(&self, (top, bottom): (Top, usize), (upper, lower): (Top, usize)) -> Step {
        let (top, upper) = (self.top(top, self.entered()), self.top(upper, &self.locals));
        let (bottom, lower) = (&self.entered()[bottom], &self.locals[lower]);
        let (Some(raised), Some(dropped)) = (excess(&upper, &top), excess(bottom, lower)) else {
            return Step::Unknown;
        };
        let ordered = |below: &Local, above: &Local| excess(below, above).is_some_and(|by| by <= 0);
        let widened = raised.saturating_add(dropped);
        if widened < 0 && (ordered(bottom, &top) || ordered(lower, &upper)) {
            Step::Smaller
        } else if widened <= 0 {
            Step::Same
        } else {
            Step::Unknown
        }
    }

    /// What a gap's top is: one of `locals`, a number bound here, which is
    /// what guards learned of, or else a number alone. A number is bound
    /// here only where it was bound before the call: past where the
    /// bindings have reached, the local it will be may be anything an arm
    /// binds, so it is that local only where it is the number.
    fn top(&self, top: Top, locals: &[Local]) -> Local {
        let value = match top {
            Top::Parameter(at) => return locals[at].clone(),
            Top::Number { value, .. } => value,
        };
        let entered = self.entered();
        let bound = self.frame.gaps.iter().find_map(|&(held, _)| match held {
            Top::Number { value: here, local }
                if here == value && entered.get(local).and_then(exact) == Some(value) =>
            {
                Some(local)
            }
            _ => None,
        });
        if let Some(local) = bound {
            return entered[local].clone();
        }
        let value = i64::try_from(value).unwrap_or(i64::MAX);
        Local {
            deep: self.frame.most(value),
            long: self.frame.most(value),
            least: self.frame.least(value),
            ..Local::unknown()
        }
    }
}

/// The natural a local is, where it is known outright.
fn exact(local: &Local) -> Option<u64> {
    let most = local.long.first().copied().flatten()?;
    let least = local.least.first().copied().flatten()?;
    (most == least).then(|| u64::try_from(most).ok()).flatten()
}

/// How much larger `x` can be than `y`, at most: the least, over every
/// key both speak of, of `x`'s upper bound less `y`'s lower.
fn excess(x: &Local, y: &Local) -> Option<i64> {
    x.value()
        .iter()
        .zip(&y.least)
        .filter_map(|(most, least)| Some(most.as_ref()?.saturating_sub(*least.as_ref()?)))
        .min()
}

/// Close the call matrices of a round, read in one tier, and answer whether
/// every repeatable path descends. A call of one of `passing` is read in
/// place, a few deep.
fn descends(
    program: &Program,
    round: &[FnId],
    passing: &HashSet<FnId>,
    operations: &[Option<Operation>],
    tier: Tier<'_>,
) -> bool {
    let within: HashSet<FnId> = round.iter().copied().collect();
    let direct = round.iter().flat_map(|id| {
        program.function(*id).body().map_or_else(Vec::new, |_| {
            let mut reader = Reader::new(program, *id, &within, operations, tier);
            reader.passing = Some(passing);
            reader.answer();
            reader.held
        })
    });
    let passed = passed_through(direct.collect(), round);
    Closure::new().proves(passed).is_ok()
}

/// The same calls with each definition the round only passes through
/// gone: where one does not call itself, every way into it is composed
/// with every way out, which says of the paths through it all they said.
/// A path that goes round forever still meets a definition kept, and
/// infinitely often, so whether every one descends is unchanged; but the
/// closure is over fewer definitions, and a join going on past a branch is
/// one way in. Only a definition with no more ways through than in and out
/// goes, so there are never more graphs than before.
fn passed_through(graphs: Vec<(Graph, ExprId)>, round: &[FnId]) -> Vec<(Graph, ExprId)> {
    let mut graphs = graphs;
    let mut kept: Vec<FnId> = round.to_vec();
    loop {
        let through = kept.iter().copied().find(|&id| {
            let into = graphs
                .iter()
                .filter(|(graph, _)| graph.callee == id)
                .count();
            let out = graphs
                .iter()
                .filter(|(graph, _)| graph.caller == id)
                .count();
            let looped = graphs
                .iter()
                .any(|(graph, _)| graph.caller == id && graph.callee == id);
            kept.len() > 1 && !looped && into * out <= into + out
        });
        let Some(id) = through else {
            return graphs;
        };
        kept.retain(|&held| held != id);
        let (touching, apart): (Vec<_>, Vec<_>) = graphs
            .into_iter()
            .partition(|(graph, _)| graph.caller == id || graph.callee == id);
        let mut composed: Vec<(Graph, ExprId)> = Vec::new();
        for (into, call) in touching.iter().filter(|(graph, _)| graph.callee == id) {
            for (out, _) in touching.iter().filter(|(graph, _)| graph.caller == id) {
                let path = compose(into, out);
                if !composed.iter().any(|(held, _)| *held == path) {
                    composed.push((path, *call));
                }
            }
        }
        graphs = apart;
        graphs.extend(composed);
    }
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
