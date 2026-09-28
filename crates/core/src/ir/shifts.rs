//! Shifts by a distance worked out while the program runs, written as a
//! loop of shifts by one place where a target has no instruction for them,
//! where the value is wider than its word and splitting will hold it as
//! several -- a shift by one is what splitting knows how to carry across --
//! or where a shift down may be by the word or more, which an instruction
//! takes modulo the word. A target that shifts by a register is handed
//! only shifts it can do in one instruction.

use super::rewrite::{self, Pass, Rebuild};
use super::{Binary, Builder, Direction, Op, Program, Relation, ValueId};

/// `program` with every shift by a worked-out distance a target on words of
/// `word_bits` cannot do in one instruction -- all of them, where `native`
/// says it has none -- written as a loop.
#[must_use]
pub fn expand_shifts(program: &Program, word_bits: u16, native: bool) -> Program {
    rewrite::rebuild(program, &mut Expand { word_bits, native })
}

struct Expand {
    word_bits: u16,
    native: bool,
}

impl Pass for Expand {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let Op::Binary {
            op: op @ (Binary::ShiftUp | Binary::ShiftDown),
            left,
            right,
        } = op
        else {
            return false;
        };
        let class = rebuild.source().class(results[0]);
        let wide = class.width().is_some_and(|bits| bits > self.word_bits);
        // An instruction moves by the distance modulo the word, which is the
        // distance itself where it is below the word. Up, a value moved a
        // word or more fits only where it is nought, which that answers too.
        let below = rebuild
            .source()
            .class(right)
            .facts()
            .and_then(|facts| facts.high)
            .is_some_and(|most| most < u64::from(self.word_bits));
        if self.native && !wide && (op == Binary::ShiftUp || below) {
            return false;
        }
        let direction = if op == Binary::ShiftUp {
            Direction::Up
        } else {
            Direction::Down
        };
        let value = rebuild.value(left);
        let value = if b.class(value) == class {
            value
        } else {
            b.convert(class, value)
        };
        let answer = looped(b, direction, value, rebuild.value(right));
        rebuild.stands_for(results[0], answer);
        true
    }
}

/// `value` moved `count` places, a place at a time.
fn looped(b: &mut Builder, direction: Direction, value: ValueId, count: ValueId) -> ValueId {
    let (class, counted) = (b.class(value), b.class(count));
    b.loop_(&[value, count], &[class], |b, state| {
        let (value, count) = (state[0], state[1]);
        let zero = b.constant(counted, 0);
        let done = b.compare(Relation::Equal, count, zero);
        b.if_(done, &[], |b| b.break_(&[value]), |b| b.yield_(&[]));
        let moved = b.shift(class, direction, value, 1);
        let one = b.constant(counted, 1);
        let rest = b.binary_at(counted, Binary::Sub, count, one);
        b.continue_(&[moved, rest]);
    })[0]
}
