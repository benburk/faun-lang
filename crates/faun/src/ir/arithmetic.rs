//! Preserve arithmetic and its range-selected classes until target selection.
//! Only monus needs a portable guard around machine subtraction.

use super::{Binary, Builder, Class, Relation, ValueId};
use crate::barb::Operation;

pub(super) fn widest(a: Class, b: Class) -> Class {
    match (a, b) {
        (Class::Natural, _) | (_, Class::Natural) => Class::Natural,
        (Class::Word, _) | (_, Class::Word) => Class::Word,
        (Class::Fixed { bits: a }, Class::Fixed { bits: b }) => Class::Fixed { bits: a.max(b) },
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
    let class = widest(result, widest(b.class(left), b.class(right)));
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
