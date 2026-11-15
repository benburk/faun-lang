//! Arithmetic on numbers a word at a time, in nothing but a word's own
//! arithmetic, which wraps: what both the natural runtime's digits and a
//! number split into words are added, taken and multiplied with.
//!
//! A carry out of a sum is the sum coming out less than what was added, and
//! a digit's product with another is worked out from the halves of each,
//! each product of halves fitting a word. A target free to do better -- an
//! add with carry, a multiply answering both words -- sees the pattern
//! where it lowers these.

use super::{Binary, Builder, Class, Direction, Relation, ValueId};

const W: Class = Class::Word;

/// `x + y + carry` for words: the word of the sum, and what it carries,
/// which is nought, one or two. Each add wraps, and came out less than what
/// it added exactly where it carried. Where `carry` is at most one, at most
/// one of the two adds carries.
pub(super) fn add_carry(
    b: &mut Builder<'_>,
    x: ValueId,
    y: ValueId,
    carry: ValueId,
) -> (ValueId, ValueId) {
    let partial = b.binary(Binary::Add, x, y);
    let first = b.compare(Relation::Less, partial, x);
    let sum = b.binary(Binary::Add, partial, carry);
    let second = b.compare(Relation::Less, sum, partial);
    (sum, b.binary(Binary::Add, first, second))
}

/// `x - y - borrow` for words: the word of the difference, and what it
/// borrows. Where `borrow` is at most one, at most one of the two borrows.
pub(super) fn sub_borrow(
    b: &mut Builder<'_>,
    x: ValueId,
    y: ValueId,
    borrow: ValueId,
) -> (ValueId, ValueId) {
    let partial = b.binary(Binary::Sub, x, y);
    let first = b.compare(Relation::Less, x, y);
    let difference = b.binary(Binary::Sub, partial, borrow);
    let second = b.compare(Relation::Less, partial, borrow);
    (difference, b.binary(Binary::Add, first, second))
}

/// The two words of `x * y`, low then high, on a target whose word is
/// `word_bits` wide: from the four products of their halves, each of which
/// fits a word.
pub(super) fn mul_wide(
    b: &mut Builder<'_>,
    x: ValueId,
    y: ValueId,
    word_bits: u16,
) -> (ValueId, ValueId) {
    let bits = word_bits / 2;
    let half = b.constant(W, 1 << bits);
    let [x0, y0] = [x, y].map(|v| b.binary(Binary::Mod, v, half));
    let [x1, y1] = [x, y].map(|v| b.shift(W, Direction::Down, v, bits));
    let low = b.binary(Binary::Mul, x0, y0);
    let across = b.binary(Binary::Mul, x0, y1);
    let back = b.binary(Binary::Mul, x1, y0);
    let high = b.binary(Binary::Mul, x1, y1);
    // The two middle products may carry past the word, which is a whole
    // half-word's worth of the high word.
    let middle = b.binary(Binary::Add, across, back);
    let middle_carry = b.compare(Relation::Less, middle, across);
    let shifted = b.shift(W, Direction::Up, middle, bits);
    let lo = b.binary(Binary::Add, low, shifted);
    let low_carry = b.compare(Relation::Less, lo, low);
    let upper = b.shift(W, Direction::Down, middle, bits);
    let carried = b.shift(W, Direction::Up, middle_carry, bits);
    let hi = b.binary(Binary::Add, high, upper);
    let hi = b.binary(Binary::Add, hi, carried);
    (lo, b.binary(Binary::Add, hi, low_carry))
}
