//! What a number can be, worked out from what a program does with it.
//!
//! A type says a value is a number and nothing about which numbers, so
//! deciding how wide to hold one is deciding what it could be. That is a
//! question about terms, not about storage: `Succ` is one more than what it
//! wraps, a match on `Zero` says which argument is nought in which arm, and
//! a call answers whatever the name it calls does. None of it needs a word
//! size, which is why it is worked out here and read below.
//!
//! It is worked out in three stages (`notes/machine/ranges.md`). Each
//! definition is read once into a numeric program ([`super::numeric`]),
//! which keeps only what bears on numbers, and each statement the Barb term
//! it came from. A solver ([`super::solve`]) works out every value of it,
//! with intervals and, where values are related, an octagon besides. And
//! what it found is mapped back here to the terms, definitions and fields
//! the tier below reads, as [`Ranges`].
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

use super::model::{CtorId, FnId, TypeId};
use super::numeric::Numeric;
use super::octagon::{Intervals, Octagon, Zone};
use super::program::Program;
use super::solve::{Scope, Solution, solve};
use super::{Shape, shape, single_field};
pub use crate::facts::Facts as Bounds;

/// Final conservative ranges consumed by lowering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Ranges {
    /// What each term answers, by the term.
    pub terms: Vec<Bounds>,
    pub matched: Vec<Bounds>,
    pub arguments: Vec<Vec<Bounds>>,
    /// What each definition is handed, by definition.
    pub takes: Vec<Vec<Bounds>>,
    /// And what each answers.
    pub answers: Vec<Bounds>,
    /// What each constructor field holds, by its place in the field pool.
    pub fields: Vec<Bounds>,
}

/// Which relations range analysis keeps: octagons in loops where nothing
/// says, and `FAUN_RANGES` chooses `octagons` everywhere, `zones` or
/// `intervals`, for measuring what each costs and earns.
fn solved(numeric: &Numeric) -> Solution {
    match std::env::var("FAUN_RANGES").as_deref() {
        Ok("octagons") => solve::<Octagon>(numeric, Scope::Everywhere),
        Ok("zones") => solve::<Zone>(numeric, Scope::Everywhere),
        Ok("intervals") => solve::<Intervals>(numeric, Scope::Everywhere),
        _ => solve::<Octagon>(numeric, Scope::Loops),
    }
}

pub(super) fn analyze(
    program: &Program,
    recognised: &super::facts::Recognised,
    assumed: &Assumed,
) -> Ranges {
    let numeric = super::numeric::extract(program, recognised, assumed);
    mapped(program, assumed, solved(&numeric))
}

/// What the solver found, as the tier below reads it. A term nothing
/// reached is a term nothing knows, and so is a parameter nothing was ever
/// handed.
fn mapped(program: &Program, assumed: &Assumed, solution: Solution) -> Ranges {
    let takes = solution
        .takes
        .into_iter()
        .enumerate()
        .map(|(at, takes)| {
            let params = program.params(FnId::at(at)).len();
            takes.map_or_else(
                || vec![Bounds::ANY; params],
                |takes| takes.into_iter().map(|held| anything(Some(held))).collect(),
            )
        })
        .collect();
    let mut fields: Vec<_> = solution.slots.into_iter().map(anything).collect();
    // A spine's rest is read as a step of its count, not as what was built
    // there, so nothing is said of that field.
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
    let known = |held: Vec<Bounds>| held.into_iter().map(|held| anything(Some(held))).collect();
    Ranges {
        terms: known(solution.terms),
        matched: known(solution.matched),
        arguments: solution.arguments.into_iter().map(known).collect(),
        takes,
        answers: solution.answers.into_iter().map(anything).collect(),
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
    /// Whether a recognized float operation is answered by a machine rather
    /// than by its body. This selects native float lowering and range
    /// assumptions; semantic recognition still reads the operation.
    pub floats: bool,
}

impl Assumed {
    pub(super) fn result(&self, id: FnId) -> Bounds {
        self.results
            .iter()
            .find(|(of, _)| *of == id)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    pub(super) fn parameter(&self, at: usize) -> Bounds {
        self.parameters
            .iter()
            .find(|(of, _)| *of == at)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    pub(super) fn field(&self, ctor: CtorId, at: usize) -> Bounds {
        self.fields
            .iter()
            .find(|(of, place, _)| *of == ctor && *place == at)
            .map_or(Bounds::ANY, |(_, _, bounds)| *bounds)
    }

    /// What a value of `ty` built outside is: anything, but for what is
    /// assumed of the one field of each wrapper it is held through. A wrapper
    /// is its field, so that bounds the value itself.
    pub(super) fn value(&self, program: &Program, ty: TypeId) -> Bounds {
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
pub(super) fn field_slots(program: &Program) -> usize {
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

/// The values any of these constants can represent, using the same join as a
/// match. For a sequence or a transparent wrapper around one, this is its
/// element count. An empty set has no possible value.
#[must_use]
pub fn bounds_of_constants<'a>(
    program: &Program,
    values: impl IntoIterator<Item = super::Constant<'a>>,
) -> Bounds {
    values.into_iter().fold(Bounds::NOTHING, |held, value| {
        held.or(super::numeric::constant_bounds(program, value))
    })
}
