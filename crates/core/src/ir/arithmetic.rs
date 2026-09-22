//! Preserve arithmetic and its range-selected classes until target selection.
//! Only monus needs a portable guard around machine subtraction.

use super::{Binary, Builder, Class, Relation, ValueId};
use crate::barb::Operation;

pub(super) fn widest(a: Class, b: Class) -> Class {
    match (a, b) {
        (Class::Natural, _) | (_, Class::Natural) => Class::Natural,
        (Class::Word, _) | (_, Class::Word) => Class::Word,
        // What either can be, which is narrower than the wider of the two
        // wherever the two say more than a width does.
        (Class::Held(a), Class::Held(b)) => Class::Held(a.or(b)),
        _ => a,
    }
}

/// A value read as `class`.
///
/// One already narrow enough is read as it stands: a class is what a value
/// can be, so anything that fits is already something this reads. Only a
/// value that does not fit is converted, which is what `met` says about the
/// same question one tier along -- and what the two of them agreeing saves
/// is a width change that changes no width.
/// A class with room for every value either of two can be.
///
/// Not a class either of them is: what a sum can be is narrower than what
/// it is worked out in, and the tier above said which. This answers only
/// the room.
fn room(a: Class, b: Class) -> Class {
    match (a, b) {
        (Class::Natural, _) | (_, Class::Natural) => Class::Natural,
        (Class::Word, _) | (_, Class::Word) => Class::Word,
        (Class::Held(a), Class::Held(b)) => Class::Held(crate::facts::Facts {
            low: 0,
            high: a.high.zip(b.high).map(|(a, b)| a.max(b)),
        }),
        _ => a,
    }
}

fn at(b: &mut Builder, value: ValueId, class: Class) -> ValueId {
    if b.class(value).fits(class) {
        value
    } else {
        b.convert(class, value)
    }
}

pub(super) fn compare(
    b: &mut Builder,
    relation: Relation,
    left: ValueId,
    right: ValueId,
) -> ValueId {
    let class = widest(b.class(left), b.class(right));
    let left = at(b, left, class);
    let right = at(b, right, class);
    b.compare(relation, left, right)
}

pub(super) fn lower(
    b: &mut Builder,
    op: Operation,
    result: Class,
    left: ValueId,
    right: ValueId,
) -> ValueId {
    // Where the answer lives, if there is room there for what either side
    // brings: then nothing is converted afterwards and the answer says what
    // the tier above proved it can be, rather than what it needed room for.
    // Otherwise somewhere with the room, and narrowed after.
    let brought = room(b.class(left), b.class(right));
    let class = if brought.fits(result) {
        result
    } else {
        room(result, brought)
    };
    let left = at(b, left, class);
    let right = at(b, right, class);
    // An operand may be narrower than the width the answer is worked out
    // at, so the width is said rather than taken from whichever operand
    // happens to be on the left.
    let answer = match op {
        Operation::Add => b.binary_at(class, Binary::Add, left, right),
        Operation::Monus => monus(b, class, left, right),
        Operation::Mul => b.binary_at(class, Binary::Mul, left, right),
        Operation::Div => b.binary_at(class, Binary::Div, left, right),
        Operation::Mod => b.binary_at(class, Binary::Mod, left, right),
        Operation::Equals { .. } | Operation::LessThan { .. } => {
            unreachable!("comparison lowered separately")
        }
    };
    at(b, answer, result)
}

fn monus(b: &mut Builder, class: Class, left: ValueId, right: ValueId) -> ValueId {
    let less = b.compare(Relation::Less, left, right);
    b.if_(
        less,
        &[class],
        |b| {
            let zero = b.constant(class, 0);
            b.yield_(&[zero]);
        },
        |b| {
            let value = b.binary_at(class, Binary::Sub, left, right);
            b.yield_(&[value]);
        },
    )[0]
}
