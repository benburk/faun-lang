//! Preserve arithmetic and its range-selected classes until target selection.

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
    if op == Operation::Monus {
        return monus(b, result, left, right);
    }
    if op == Operation::Pow {
        return shifted_one(b, result, left, right)
            .unwrap_or_else(|| power(b, result, left, right));
    }
    // Where the answer lives, if there is room there for what either side
    // brings: then nothing is converted afterwards and the answer says what
    // the tier above proved it can be, rather than what it needed room for.
    // Otherwise somewhere with the room, and narrowed after.
    let brought = room(b.class(left), b.class(right));
    // A bitwise or can set bits neither side's greatest has, but none
    // above the wider's top bit.
    let brought = match (op, brought) {
        (Operation::Or | Operation::Xor, Class::Held(held)) => {
            Class::Held(held.merged(crate::facts::Facts::at(0), false))
        }
        _ => brought,
    };
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
        Operation::Mul => b.binary_at(class, Binary::Mul, left, right),
        Operation::Div => b.binary_at(class, Binary::Div, left, right),
        Operation::Mod => b.binary_at(class, Binary::Mod, left, right),
        Operation::And => b.binary_at(class, Binary::And, left, right),
        Operation::Or => b.binary_at(class, Binary::Or, left, right),
        Operation::Xor => b.binary_at(class, Binary::Xor, left, right),
        Operation::Monus | Operation::Pow => unreachable!("lowered above"),
        Operation::Equals { .. } | Operation::LessThan { .. } => {
            unreachable!("comparison lowered separately")
        }
    };
    at(b, answer, result)
}

/// A monus reads its operands as a comparison does, and answers at the
/// class the tier above proved, which may be narrower than either operand:
/// the answer is never more than `left`. Only a natural's monus answers a
/// natural, so a machine answer to one is converted afterwards.
fn monus(b: &mut Builder, result: Class, left: ValueId, right: ValueId) -> ValueId {
    let class = widest(b.class(left), b.class(right));
    let left = at(b, left, class);
    let right = at(b, right, class);
    let natural = class == Class::Natural;
    if natural == (result == Class::Natural) {
        return b.binary_at(result, Binary::Monus, left, right);
    }
    let answer = b.binary_at(class, Binary::Monus, left, right);
    at(b, answer, result)
}

/// Two to a power, at a class a machine holds, is one moved up that many
/// places.
fn shifted_one(
    b: &mut Builder,
    result: Class,
    base: ValueId,
    exponent: ValueId,
) -> Option<ValueId> {
    if b.known_number(base) != Some(2)
        || !matches!(result, Class::Held(_) | Class::Word)
        || !b.class(exponent).fits(result)
    {
        return None;
    }
    let one = b.constant(result, 1);
    Some(b.binary_at(result, Binary::ShiftUp, one, exponent))
}

/// `base` to the power of `exponent`, by squaring: a bit of the exponent a
/// step, from the bottom, multiplying in the base's power for each bit
/// that is set.
///
/// Everything is worked out at the answer's class, which the tier above
/// proved it fits. That holds for every step as well: what has been
/// multiplied in is the base to the power of the exponent's low bits, and
/// the base is squared only while bits are left above, so neither is ever
/// more than the answer.
fn power(b: &mut Builder, result: Class, base: ValueId, exponent: ValueId) -> ValueId {
    // Loop state is held at one class throughout, which is the answer's
    // even where the base alone is narrower.
    let base = if b.class(base) == result {
        base
    } else {
        b.convert(result, base)
    };
    let one = b.constant(result, 1);
    let bit = Class::fixed(1);
    let counted = b.class(exponent);
    b.loop_(&[one, base, exponent], &[result], |b, state| {
        let [built, base, exponent] = [state[0], state[1], state[2]];
        let zero = b.constant(counted, 0);
        let done = compare(b, Relation::Equal, exponent, zero);
        b.if_(done, &[], |b| b.break_(&[built]), |b| b.yield_(&[]));
        let two = b.constant(Class::fixed(2), 2);
        let low = lower(b, Operation::Mod, bit, exponent, two);
        let built = b.if_(
            low,
            &[result],
            |b| {
                let product = b.binary_at(result, Binary::Mul, built, base);
                b.yield_(&[product]);
            },
            |b| b.yield_(&[built]),
        )[0];
        let rest = lower(b, Operation::Div, counted, exponent, two);
        let zero = b.constant(counted, 0);
        let last = compare(b, Relation::Equal, rest, zero);
        let base = b.if_(
            last,
            &[result],
            |b| b.yield_(&[base]),
            |b| {
                let square = b.binary_at(result, Binary::Mul, base, base);
                b.yield_(&[square]);
            },
        )[0];
        b.continue_(&[built, base, rest]);
    })[0]
}
