//! Recognising what lowering had no way to avoid writing.
//!
//! Lowering answers one question per place. A comparison is asked what value
//! it is, and answers with the tag of a constructor; a match is asked which
//! constructor it has, and asks for the tag. Neither knows it is standing
//! next to the other, so between them a condition becomes a number and the
//! number becomes a condition again. Reading both at once is what this is
//! for, and it is the tier below's last chance before three targets each
//! find the same thing out separately.
//!
//! The same for a constant. A constant is written as narrow as its value
//! needs, since that is what the tier above proved about it, and then read
//! at whatever width the thing reading it holds. Writing it at that width to
//! begin with says the same and asks a target for nothing.
//!
//! And the same for a run of them. Barb combines calls it recognizes as
//! arithmetic, but lowering can still introduce constructor steps and callers
//! can build machine IR directly. Here four steps of one become a step of
//! four regardless of where they came from.
//!
//! And the same for a condition asked twice. Lowering a match on what a
//! branch answered asks the branch's own condition again, and in each arm of
//! the second asking, what the first answered is what its arm on the same
//! side did: a number, or something worked out before either. Read that way,
//! the first branch answers nothing anybody reads.
//!
//! And the same for a difference that stops at nought, asked whether it is
//! nought: that is asking whether one number is no more than another, which
//! is one comparison rather than a subtraction and a test.
//!
//! And the same for a word's arithmetic worked out as a natural. A sum or a
//! product of two sixty-four-bit words taken modulo 2^64, which is what a
//! `U64`'s is, has nowhere narrower than a natural to be worked out before
//! the remainder, as a `U32`'s is worked out at sixty-four bits. But the
//! low bits of a sum or a product are the sum or product of the low bits,
//! so read at sixty-four bits it is worked out there, at a class that
//! wraps, and the natural and its remainder go.
//!
//! And the same for arithmetic on numbers known before the program runs,
//! which legalization writes a great deal of: an offset is a count of words
//! times a word's bytes, plus a header, plus which leaf. Two known numbers
//! are one, and adding nought or multiplying by one is what was there. At a
//! machine word's width that is worked out modulo the word, which only a
//! program whose layout is bound says how wide it is; a class that is a fit
//! requirement is worked out exactly, and left alone where the answer would
//! not fit it.

use num_bigint::BigUint;

use crate::facts::Facts;

use super::{
    Binary, Builder, Class, Direction, Exit, Op, Program, RegionId, Relation, ValueId, model::wrap,
    rewrite,
};

/// The fewest bits a machine word has on any target this compiles for.
///
/// A shift by fewer places than that is one every target takes as written. A
/// machine asked to move a value further than it is wide does not answer
/// nought: it takes the distance modulo its own width and answers something
/// else entirely, so a distance this tier cannot vouch for is left as the
/// product or quotient it was.
const WORD_FLOOR: u16 = 16;

/// How deep [`Simplify::low`] looks under a conversion: deeper than any
/// expression a program writes on one line, and shallow enough that a long
/// chain of sums does not recurse without end.
const LOW_DEPTH: u8 = 32;

/// Rebuild `source` with those shapes read as what they mean.
///
/// What stops being read is left where it stands; [`super::prune`] is what
/// takes it away.
#[must_use]
pub(super) fn simplify(source: &Program) -> Program {
    let mut pass = Simplify {
        wrote: Wrote::of(source),
        steps: vec![None; source.values_count()],
        folded: vec![None; source.values_count()],
        word_bits: source.layout.map(|layout| layout.word_bits),
    };
    rewrite::rebuild(source, &mut pass)
}

struct Simplify {
    wrote: Wrote,
    /// What each old value is a fixed step past, once anything has been
    /// found to be a step past anything. Written as the walk goes, since
    /// what a step is past is whatever the walk has already written.
    steps: Vec<Option<Step>>,
    /// What each old value comes to where it was worked out here from
    /// numbers known before the program runs.
    folded: Vec<Option<u64>>,
    /// How wide a machine word is, where the program says.
    word_bits: Option<u16>,
}

/// A value reached by adding a known number to another value, all at one
/// width. The width is part of it: a step taken wider than the one before
/// asserts something the narrower one did not.
///
/// The width and not the class. Two steps of a run are held at what each
/// can be, which differs along the run even where the room they need does
/// not, and what a step asserts is the room.
#[derive(Clone, Copy)]
struct Step {
    from: ValueId,
    by: u64,
    width: Option<u16>,
}

impl rewrite::Pass for Simplify {
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per shape the pass recognises"
    )]
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        if let Op::Binary { op, left, right } = op
            && self.folding(rebuild, b, op, [left, right], results[0])
        {
            return true;
        }
        match op {
            Op::CellField { cell, index, shape } => {
                let Some((
                    Op::Cell {
                        fields,
                        shape: made,
                        ..
                    },
                    _,
                    _,
                )) = self.wrote.0[cell.index()]
                else {
                    return false;
                };
                if shape != made {
                    return false;
                }
                let index = usize::try_from(index).expect("a validated field index");
                let field = rebuild.source().values(fields)[index];
                let held = rebuild.value(field);
                if !b.class(held).fits(rebuild.source().class(results[0])) {
                    return false;
                }
                // The field is already evaluated, even if constructing the
                // temporary cell was its only other use. Pruning the cell
                // must not prune an effect that produced one of its fields.
                rebuild.stands_for(results[0], held);
                true
            }
            Op::CellTag { cell } => {
                let Some((Op::Cell { tag, .. }, _, _)) = self.wrote.0[cell.index()] else {
                    return false;
                };
                let held = b.constant(Class::Word, u64::from(tag));
                rebuild.stands_for(results[0], held);
                true
            }
            Op::Convert { value } => {
                let class = rebuild.source().class(results[0]);
                self.wrapping(rebuild, b, class, value, results[0])
                    || self.widened(rebuild, b, class, value, results[0])
            }
            Op::Binary {
                op: Binary::Add,
                left,
                right,
            } => {
                // A value added to itself is that value moved up one place,
                // whatever it is. Anything else may be a step, and a run of
                // steps folds into one where a shift would end it.
                (left == right && shifting(rebuild, b, Direction::Up, left, 1, results[0]))
                    || self.stepping(rebuild, b, left, right, results[0])
            }
            Op::Binary {
                op: Binary::Mul,
                left,
                right,
            } => {
                self.places(right)
                    .is_some_and(|by| shifting(rebuild, b, Direction::Up, left, by, results[0]))
                    || self.moved(rebuild, b, (Binary::ShiftUp, left, right), results[0])
                    || self.moved(rebuild, b, (Binary::ShiftUp, right, left), results[0])
            }
            Op::Binary {
                op: Binary::Div,
                left,
                right,
            } => {
                self.places(right)
                    .is_some_and(|by| shifting(rebuild, b, Direction::Down, left, by, results[0]))
                    || self.moved(rebuild, b, (Binary::ShiftDown, left, right), results[0])
            }
            Op::Binary {
                op: Binary::Mod,
                left,
                right,
            } => self.remainder(rebuild, b, left, right, results[0]),
            Op::If {
                condition,
                then_region,
                else_region,
            } => self.branching(rebuild, b, condition, [then_region, else_region], results),
            Op::Compare {
                relation: Relation::Equal,
                left,
                right,
            } => self.at_most(rebuild, b, left, right, results[0]),
            _ => false,
        }
    }
}

/// A product or quotient by a power of two, and a value added to itself,
/// written as the shift each of them is.
///
/// Every target has an instruction for this and none has one for the
/// product, so leaving it a product is asking three backends for a loop
/// where one instruction does. The answer is the same and so is the
/// class: a shift neither widens nor narrows, and what it may come to is
/// the fit requirement the product already carried.
///
/// Only over a value the machine holds. An arbitrary-precision natural
/// has no width to move within, and its products go to the helpers.
fn shifting(
    rebuild: &rewrite::Rebuild<'_>,
    b: &mut Builder,
    direction: Direction,
    value: ValueId,
    by: u32,
    result: ValueId,
) -> bool {
    let class = rebuild.source().class(result);
    if !matches!(class, Class::Held(_) | Class::Word) {
        return false;
    }
    let Ok(by) = u16::try_from(by) else {
        return false;
    };
    if by == 0 || by >= class.width().unwrap_or(WORD_FLOOR) {
        return false;
    }
    let held = b.shift(class, direction, rebuild.value(value), by);
    rebuild.stands_for(result, held);
    true
}

impl Simplify {
    /// A conversion that takes nothing off, and a constant read at another
    /// width.
    ///
    /// A value already narrow enough is read where it stands. One that is
    /// not, and is a number known before the program runs, is written at the
    /// width it is read at -- where that width is one this tier knows, which
    /// a machine word's is not.
    fn widened(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        class: Class,
        value: ValueId,
        result: ValueId,
    ) -> bool {
        // A value already narrow enough is read as it stands: what it can
        // be, the wider class admits, so nothing happens in between. What it
        // is held at is asked of the program being written, since a rule
        // before this one may have made it narrower than it was.
        let held = rebuild.value(value);
        if b.class(held).fits(class) {
            rebuild.stands_for(result, held);
            return true;
        }
        let Some(number) = self.number(value) else {
            return false;
        };
        if !matches!(class, Class::Held(_)) {
            return false;
        }
        rebuild.stands_for(result, b.constant(class, wrap(class, number)));
        true
    }

    /// `value ∸ bound == 0`, for a bound known before the program runs, as
    /// `value < bound + 1`: where the value could be that next number, so
    /// that it is held at least as wide as the number it is compared with.
    fn at_most(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        left: ValueId,
        right: ValueId,
        result: ValueId,
    ) -> bool {
        if self.number(right) != Some(0) {
            return false;
        }
        let Some((
            Op::Binary {
                op: Binary::Monus,
                left: value,
                right: bound,
            },
            _,
            _,
        )) = self.wrote.0[left.index()]
        else {
            return false;
        };
        let Some(next) = self.number(bound).and_then(|bound| bound.checked_add(1)) else {
            return false;
        };
        let reaches = match rebuild.source().class(value) {
            Class::Word => self
                .word_bits
                .is_some_and(|bits| bits >= 64 || next >> bits == 0),
            class => class
                .facts()
                .and_then(|facts| facts.high)
                .is_some_and(|high| next <= high),
        };
        if !reaches {
            return false;
        }
        let next = b.constant(
            Class::Held(Facts {
                low: next,
                high: Some(next),
            }),
            next,
        );
        let less = b.compare(Relation::Less, rebuild.value(value), next);
        rebuild.stands_for(result, less);
        true
    }

    /// How many places a value multiplies or divides by, where it is a power
    /// of two known before the program runs.
    fn places(&self, value: ValueId) -> Option<u32> {
        let number = self.number(value)?;
        number.is_power_of_two().then(|| number.trailing_zeros())
    }

    /// The number an old value is, where a constant wrote it or it was
    /// worked out here from ones.
    fn number(&self, value: ValueId) -> Option<u64> {
        self.wrote
            .number(value)
            .or_else(|| self.folded[value.index()])
    }

    /// Arithmetic whose answer is known, or is one of its operands.
    fn folding(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Binary,
        [left, right]: [ValueId; 2],
        result: ValueId,
    ) -> bool {
        let class = rebuild.source().class(result);
        if !matches!(class, Class::Word | Class::Held(_)) {
            return false;
        }
        let (x, y) = (self.number(left), self.number(right));
        if let (Some(x), Some(y)) = (x, y)
            && let Some(answer) = self.calculated(op, x, y, class)
        {
            self.folded[result.index()] = Some(answer);
            rebuild.stands_for(result, b.constant(class, answer));
            return true;
        }
        // What was there already, where it fits where it is read.
        let same = match (op, x, y) {
            (Binary::Add | Binary::Sub | Binary::Monus | Binary::Or | Binary::Xor, _, Some(0))
            | (Binary::Mul | Binary::Div, _, Some(1)) => Some(left),
            (Binary::Add | Binary::Or | Binary::Xor, Some(0), _) | (Binary::Mul, Some(1), _) => {
                Some(right)
            }
            _ => None,
        };
        if let Some(same) = same {
            let held = rebuild.value(same);
            if b.class(held).fits(class) {
                rebuild.stands_for(result, held);
                return true;
            }
        }
        if matches!(op, Binary::Mul | Binary::And) && (x == Some(0) || y == Some(0)) {
            self.folded[result.index()] = Some(0);
            rebuild.stands_for(result, b.constant(class, 0));
            return true;
        }
        false
    }

    /// What `op` answers for two known numbers at `class`: modulo a word
    /// where the class is one and the program says how wide, and exactly
    /// where the class is a fit requirement the answer meets.
    fn calculated(&self, op: Binary, x: u64, y: u64, class: Class) -> Option<u64> {
        let answer = match class {
            Class::Word => {
                let bits = self.word_bits?;
                let answer = match op {
                    Binary::Add => x.wrapping_add(y),
                    Binary::Sub => x.wrapping_sub(y),
                    Binary::Monus => x.saturating_sub(y),
                    Binary::Mul => x.wrapping_mul(y),
                    Binary::Div => x.checked_div(y).unwrap_or(0),
                    Binary::Mod => x.checked_rem(y).unwrap_or(x),
                    Binary::And => x & y,
                    Binary::Or => x | y,
                    Binary::Xor => x ^ y,
                    Binary::ShiftUp | Binary::ShiftDown => return None,
                };
                return Some(if bits >= 64 {
                    answer
                } else {
                    answer & ((1 << bits) - 1)
                });
            }
            _ => match op {
                Binary::Add => x.checked_add(y)?,
                Binary::Sub => x.checked_sub(y)?,
                Binary::Monus => x.saturating_sub(y),
                Binary::Mul => x.checked_mul(y)?,
                Binary::Div => x.checked_div(y).unwrap_or(0),
                Binary::Mod => x.checked_rem(y).unwrap_or(x),
                Binary::And => x & y,
                Binary::Or => x | y,
                Binary::Xor => x ^ y,
                Binary::ShiftUp => x
                    .checked_shl(u32::try_from(y).ok()?)
                    .filter(|m| m >> y == x)?,
                Binary::ShiftDown => x.checked_shr(u32::try_from(y).ok()?).unwrap_or(0),
            },
        };
        (wrap(class, answer) == answer).then_some(answer)
    }

    /// A product or quotient by one moved up some places, which is its
    /// value moved that many places: where `power` was written as one
    /// moved up, `value` moved up or down by as many.
    fn moved(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        (op, value, power): (Binary, ValueId, ValueId),
        result: ValueId,
    ) -> bool {
        let Some((
            Op::Binary {
                op: Binary::ShiftUp,
                left,
                right,
            },
            ..,
        )) = self.wrote.0[power.index()]
        else {
            return false;
        };
        let class = rebuild.source().class(result);
        let by = rebuild.value(right);
        if self.number(left) != Some(1) || !b.class(by).fits(class) {
            return false;
        }
        // A product at a class that wraps may lose its top bits, which a
        // shift by a worked-out distance may not.
        if op == Binary::ShiftUp && class.wraps() {
            return false;
        }
        let moved = b.binary_at(class, op, rebuild.value(value), by);
        rebuild.stands_for(result, moved);
        true
    }

    /// A remainder by a power of two is the bits below it, which is what
    /// reading a value at that width already means.
    ///
    /// This is how a language whose only number counts without a last step
    /// says a machine word. Left as a remainder it is a division: on a
    /// machine with no divide instruction, a loop over every bit of it.
    fn remainder(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        left: ValueId,
        right: ValueId,
        result: ValueId,
    ) -> bool {
        let Some(by) = self.number(right) else {
            return false;
        };
        if !by.is_power_of_two() {
            return false;
        }
        let Ok(bits) = u16::try_from(by.trailing_zeros()) else {
            return false;
        };
        // Narrower than what the remainder was worked out at, which is what
        // taking a remainder does and what anything reading it allows.
        let class = Class::fixed(bits);
        rebuild.stands_for(result, b.convert(class, rebuild.value(left)));
        true
    }

    /// A natural sum, difference or product read as a machine number,
    /// worked out at sixty-four bits instead.
    ///
    /// What a conversion to sixty-four bits keeps of a sum is the sum of
    /// what it keeps of each side, modulo 2^64, and the same for a product,
    /// and for a difference whose right side is never the larger. So the
    /// arithmetic under one goes to a class that [wraps](Class::wraps),
    /// down to what is already held as a machine number, what a natural
    /// conversion widened, a remainder by a power of two at least as large,
    /// which keeps every bit read here, or a natural known before the
    /// program runs. Anything else is read at sixty-four bits where it
    /// stands, which is what the conversion did to all of it.
    ///
    /// Read narrower, it is the same at sixty-four bits narrowed after. A
    /// `U32`'s arithmetic is a machine's already, worked out wide enough and
    /// narrowed after; it is only that nothing is held wider than sixty-four
    /// bits that leaves a natural, and only a natural is read this way.
    fn wrapping(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        class: Class,
        value: ValueId,
        result: ValueId,
    ) -> bool {
        if !matches!(class, Class::Held(_)) || !self.computed(rebuild.source(), value) {
            return false;
        }
        let Some(low) = self.low(rebuild, b, value, LOW_DEPTH) else {
            return false;
        };
        // Narrower, what the conversion keeps of that is what it kept of
        // the whole.
        let low = if b.class(low).fits(class) {
            low
        } else {
            b.convert(class, low)
        };
        rebuild.stands_for(result, low);
        true
    }

    /// Whether a natural was worked out by arithmetic this carries to
    /// sixty-four bits. A natural that was not is read where it stands.
    fn computed(&self, source: &Program, value: ValueId) -> bool {
        let Some((Op::Binary { op, left, right }, Class::Natural, _)) = self.wrote.0[value.index()]
        else {
            return false;
        };
        op == Binary::Mod && self.keeps_low(source, right)
            || self.carried(source, op, left, right).is_some()
    }

    /// What a natural `op` of `left` and `right` is at a class that wraps,
    /// where it is the same there: a sum or a product, and a difference
    /// that never stops at nought.
    fn carried(
        &self,
        source: &Program,
        op: Binary,
        left: ValueId,
        right: ValueId,
    ) -> Option<Binary> {
        match op {
            Binary::Add | Binary::Mul => Some(op),
            Binary::Monus if self.no_less(source, left, right) => Some(Binary::Sub),
            _ => None,
        }
    }

    /// What `value` is modulo 2^64, as something written here: see
    /// [`Self::wrapping`]. Nothing where it is not a number. `depth` bounds
    /// how far down it looks, past which a value is read where it stands.
    fn low(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        value: ValueId,
        depth: u8,
    ) -> Option<ValueId> {
        let source = rebuild.source();
        let class = source.class(value);
        let wide = Class::fixed(64);
        match class {
            Class::Held(_) => return Some(rebuild.value(value)),
            Class::Word => return Some(b.convert(wide, rebuild.value(value))),
            Class::Natural => {}
            Class::Cell | Class::Buffer | Class::Address => return None,
        }
        let stands = |b: &mut Builder| Some(b.convert(wide, rebuild.value(value)));
        let Some(depth) = depth.checked_sub(1) else {
            return stands(b);
        };
        let Some((op, ..)) = self.wrote.0[value.index()] else {
            return stands(b);
        };
        match op {
            // A machine number widened: what it was is every bit kept here.
            Op::Convert { value: from } if source.class(from) != Class::Natural => {
                self.low(rebuild, b, from, depth)
            }
            Op::NaturalConstant(_) | Op::Constant { .. } => {
                let digits = self.known(source, value)?.to_u64_digits();
                let number = digits.first().copied().unwrap_or(0);
                Some(b.constant(Class::Held(Facts::at(number)), number))
            }
            Op::Binary {
                op: Binary::Mod,
                left,
                right,
            } if self.keeps_low(source, right) => self.low(rebuild, b, left, depth),
            Op::Binary { op, left, right } => match self.carried(source, op, left, right) {
                Some(op) => {
                    let left = self.low(rebuild, b, left, depth)?;
                    let right = self.low(rebuild, b, right, depth)?;
                    Some(b.binary_at(wide, op, left, right))
                }
                None => stands(b),
            },
            _ => stands(b),
        }
    }

    /// Whether `left` is never less than `right`, so that a monus of them
    /// never stops at nought: where `left` was written as something plus a
    /// number known before the program runs that is at least the most
    /// `right` can be.
    fn no_less(&self, source: &Program, left: ValueId, right: ValueId) -> bool {
        let Some((
            Op::Binary {
                op: Binary::Add,
                left: one,
                right: other,
            },
            ..,
        )) = self.wrote.0[left.index()]
        else {
            return false;
        };
        let Some(most) = self.most(source, right) else {
            return false;
        };
        [one, other]
            .into_iter()
            .filter_map(|side| self.known(source, side))
            .any(|added| added >= most)
    }

    /// The most a value can be, where its class or the machine number a
    /// natural widened says.
    fn most(&self, source: &Program, value: ValueId) -> Option<BigUint> {
        let held = match self.wrote.0[value.index()] {
            Some((Op::Convert { value: from }, Class::Natural, _)) => source.class(from),
            _ => source.class(value),
        };
        held.facts()?.high.map(BigUint::from)
    }

    /// The number a value is, natural or not, where it is known before the
    /// program runs.
    fn known(&self, source: &Program, value: ValueId) -> Option<BigUint> {
        match self.wrote.0[value.index()]? {
            (Op::NaturalConstant(data), ..) => {
                Some(BigUint::from_bytes_le(source.datum_bytes(data)))
            }
            (Op::Constant { value }, ..) => Some(BigUint::from(value)),
            (Op::Convert { value: from }, Class::Natural, _) => {
                self.number(from).map(BigUint::from)
            }
            _ => self.number(value).map(BigUint::from),
        }
    }

    /// Whether a remainder by `modulus` keeps every bit below 2^64: where it
    /// is a power of two at least that, known before the program runs.
    fn keeps_low(&self, source: &Program, modulus: ValueId) -> bool {
        self.known(source, modulus)
            .is_some_and(|number| number.count_ones() == 1 && number.bits() > 64)
    }

    /// A step past a step is one step.
    ///
    /// Every one of them is still written, since something may read a value
    /// part way along the run. What nothing reads goes when the leftovers
    /// do.
    fn stepping(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        left: ValueId,
        right: ValueId,
        result: ValueId,
    ) -> bool {
        let class = rebuild.source().class(result);
        let Some(step) = self.stepped(left, right, class) else {
            return false;
        };
        self.steps[result.index()] = Some(step);
        // The number it steps by can be nothing else, and saying so is what
        // keeps a constant from taking the range of whatever it stands
        // beside. Anything reading it has room, the run having been checked
        // to fit the width the step is taken at.
        let by = b.constant(Class::Held(Facts::at(step.by)), step.by);
        let from = rebuild.value(step.from);
        rebuild.stands_for(result, b.binary_at(class, Binary::Add, from, by));
        true
    }

    /// A branch asking which constructor a comparison answered is the
    /// comparison, with its arms in whichever order the tags say; and one
    /// on a condition an earlier branch took reads what that one answered.
    fn branching(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        condition: ValueId,
        arms: [RegionId; 2],
        results: &[ValueId],
    ) -> bool {
        let Some((test, swapped)) = self.wrote.asks(rebuild.source(), condition) else {
            return self.threading(rebuild, b, condition, arms, results);
        };
        let [then_region, else_region] = if swapped { [arms[1], arms[0]] } else { arms };
        if self.threading(rebuild, b, test, [then_region, else_region], results) {
            return true;
        }
        let test = rebuild.value(test);
        let fresh = rebuild.if_(b, test, results, then_region, else_region, self);
        for (&was, now) in results.iter().zip(fresh) {
            rebuild.stands_for(was, now);
        }
        true
    }

    /// A branch on a condition an earlier branch took: in each arm, what the
    /// earlier one answered is what its arm on the same side answered,
    /// where that is a number or something worked out before it, so the
    /// earlier one need not be asked.
    fn threading(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        condition: ValueId,
        arms: [RegionId; 2],
        results: &[ValueId],
    ) -> bool {
        let sides = self.wrote.sides(rebuild, condition);
        if sides.iter().all(Vec::is_empty) {
            return false;
        }
        let pass = std::cell::RefCell::new(&mut *self);
        let arm = |b: &mut Builder, side: usize| {
            let held: Vec<_> = sides[side]
                .iter()
                .map(|&(was, answered)| {
                    let before = rebuild.standing(was);
                    let now = match answered {
                        Answered::Number(number, class) => b.constant(class, number),
                        Answered::Before(value) => rebuild.value(value),
                    };
                    rebuild.stands_for(was, now);
                    (was, before)
                })
                .collect();
            let mut pass = pass.borrow_mut();
            rebuild.region(b, arms[side], &[], &mut **pass);
            for (was, before) in held {
                rebuild.restand(was, before);
            }
        };
        let fresh = b.if_(
            rebuild.value(condition),
            &rebuild.classes(results),
            |b| arm(b, 0),
            |b| arm(b, 1),
        );
        for (&was, now) in results.iter().zip(fresh) {
            rebuild.stands_for(was, now);
        }
        true
    }

    /// Where an addition of a known number leaves off, counting the run it
    /// continues. Nothing is answered for an addition of something worked
    /// out, or for one whose run would not fit the width it is taken at.
    fn stepped(&self, left: ValueId, right: ValueId, class: Class) -> Option<Step> {
        if !matches!(class, Class::Word | Class::Held(_)) {
            return None;
        }
        let by = self.number(right)?;
        let width = class.width();
        let held = match self.steps[left.index()] {
            Some(held) if held.width == width => Step {
                from: held.from,
                by: held.by.checked_add(by)?,
                width,
            },
            // The first step of a run, which is written as it stands and is
            // only worth knowing because of what may come after it.
            _ => Step {
                from: left,
                by,
                width,
            },
        };
        // A run wider than the width it is taken at is not the same run.
        (wrap(class, held.by) == held.by).then_some(held)
    }
}

/// What an earlier branch's arm answered, as a later one on the same
/// condition can name it: a number, or a value worked out before it.
#[derive(Clone, Copy)]
enum Answered {
    Number(u64, Class),
    Before(ValueId),
}

/// A branch's arms, then and else, and its results.
type Branch<'a> = ([RegionId; 2], &'a [ValueId]);

/// What wrote each value, and which of its results the value is, which is
/// what lets one instruction be read together with the ones it reads.
struct Wrote(
    Vec<Option<(Op, Class, usize)>>,
    Vec<Vec<([RegionId; 2], Vec<ValueId>)>>,
);

impl Wrote {
    fn of(source: &Program) -> Self {
        let mut held = vec![None; source.values_count()];
        let mut branches = vec![Vec::new(); source.values_count()];
        for function in source.functions() {
            let Some(body) = function.body() else {
                continue;
            };
            for (op, results) in every(source, body) {
                if let Op::If {
                    condition,
                    then_region,
                    else_region,
                } = op
                    && !results.is_empty()
                {
                    branches[condition.index()].push(([then_region, else_region], results.clone()));
                }
                for (at, value) in results.into_iter().enumerate() {
                    held[value.index()] = Some((op, source.class(value), at));
                }
            }
        }
        Self(held, branches)
    }

    /// Every branch answering something on `condition`.
    fn asked(&self, condition: ValueId) -> Vec<Branch<'_>> {
        self.1[condition.index()]
            .iter()
            .map(|(regions, results)| (*regions, results.as_slice()))
            .collect()
    }

    /// For each arm of a branch on `condition`, which results of an earlier
    /// branch on it stand for what there.
    fn sides(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        condition: ValueId,
    ) -> [Vec<(ValueId, Answered)>; 2] {
        let source = rebuild.source();
        let mut sides: [Vec<(ValueId, Answered)>; 2] = [Vec::new(), Vec::new()];
        for (regions, results) in self.asked(condition) {
            // One not yet written is not before this one.
            if results.iter().all(|&was| rebuild.standing(was).is_none()) {
                continue;
            }
            let inside = within(source, regions);
            for (side, held) in sides.iter_mut().enumerate() {
                let yielded = source.outgoing(regions[side]);
                for (&was, &value) in results.iter().zip(yielded) {
                    // What stands for the result must be something the
                    // result could be: an arm the tier above found is never
                    // taken may answer anything.
                    let class = source.class(was);
                    if !source.class(value).fits(class) {
                        continue;
                    }
                    let answered = match self.number(value) {
                        Some(number) => Answered::Number(number, class),
                        None if !inside.contains(&value) => Answered::Before(value),
                        None => continue,
                    };
                    held.push((was, answered));
                }
            }
        }
        sides
    }

    /// The number a value is, where a constant wrote it. A natural is held
    /// in the data pool rather than as a number here, and says nothing.
    fn number(&self, value: ValueId) -> Option<u64> {
        let (op, class, _) = self.0[value.index()]?;
        match op {
            Op::Constant { value } if matches!(class, Class::Word | Class::Held(_)) => Some(value),
            _ => None,
        }
    }

    /// Whether a condition only asks which arm an earlier branch took, by
    /// asking whether one of its results is a number one arm answers and
    /// the other cannot: if so, that branch's own condition and whether the
    /// answer runs the arms the other way round.
    fn asks(&self, source: &Program, condition: ValueId) -> Option<(ValueId, bool)> {
        let Op::Compare {
            relation: Relation::Equal,
            left,
            right,
        } = self.0[condition.index()]?.0
        else {
            return None;
        };
        let wanted = self.number(right)?;
        let (
            Op::If {
                condition: test,
                then_region,
                else_region,
            },
            _,
            at,
        ) = self.0[left.index()]?
        else {
            return None;
        };
        let taken = self.answers(source, then_region, at, wanted)?;
        let otherwise = self.answers(source, else_region, at, wanted)?;
        // Nothing is decided where both arms answer alike.
        match (taken, otherwise) {
            (true, false) => Some((test, false)),
            (false, true) => Some((test, true)),
            _ => None,
        }
    }

    /// Whether an arm's result `at` is `wanted`, where that is known: a
    /// constant says, and so does a value that cannot be it.
    fn answers(&self, source: &Program, region: RegionId, at: usize, wanted: u64) -> Option<bool> {
        let terminator = source.region(region).terminator?;
        if terminator.exit != Exit::Yield {
            return None;
        }
        let &value = source.values(terminator.values).get(at)?;
        if let Some(number) = self.number(value) {
            return Some(number == wanted);
        }
        let facts = source.class(value).facts()?;
        let outside = wanted < facts.low || facts.high.is_some_and(|high| wanted > high);
        outside.then_some(false)
    }
}

/// Every value written within a branch's arms.
fn within(source: &Program, regions: [RegionId; 2]) -> Vec<ValueId> {
    regions
        .iter()
        .flat_map(|&region| {
            let params = source.values(source.region(region).params).to_vec();
            every(source, region)
                .into_iter()
                .flat_map(|(_, results)| results)
                .chain(params)
        })
        .collect()
}

/// Every instruction under a region, each with what it writes.
fn every(source: &Program, region: RegionId) -> Vec<(Op, Vec<ValueId>)> {
    let mut held = Vec::new();
    let mut stack = vec![region];
    while let Some(region) = stack.pop() {
        for (op, results) in source.walk(region) {
            match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => stack.extend([then_region, else_region]),
                Op::Loop { body, .. } => stack.push(body),
                _ => {}
            }
            held.push((*op, results.to_vec()));
        }
    }
    held
}
