//! Select ROL when the low and high parts of a shifted word are rejoined.
//! Track uses across region boundaries so any separately read part survives.

use std::collections::{HashMap, HashSet};

use crate::WORD_BITS;
use crate::ir::{Binary, Direction, Function, Op, Program, ValueId};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Count {
    Immediate(u8),
    Register(ValueId),
}

#[derive(Clone, Copy)]
pub(super) struct Rotate {
    pub value: ValueId,
    pub bits: u16,
    pub count: Count,
}

#[derive(Default)]
pub(super) struct Plan {
    pub roots: HashMap<ValueId, Rotate>,
    pub omitted: HashSet<ValueId>,
}

impl Plan {
    pub(super) fn new(p: &Program) -> Self {
        let mut defs = vec![None; p.values_count()];
        let mut joins = Vec::new();
        for body in p.functions().iter().filter_map(Function::body) {
            for (op, results) in p.walk_within(body) {
                if let [result] = *results {
                    defs[result.index()] = Some(op);
                    if let Op::Binary {
                        op: Binary::Add | Binary::Or | Binary::Xor,
                        left,
                        right,
                    } = *op
                    {
                        joins.push((result, left, right));
                    }
                }
            }
        }
        let shapes = Shapes { p, defs: &defs };
        let mut plan = Self::default();
        for (result, left, right) in joins {
            if let Some(rotate) = shapes
                .join(left, right)
                .or_else(|| shapes.join(right, left))
            {
                plan.roots.insert(result, rotate);
            }
        }
        if !plan.roots.is_empty() {
            plan.omit_unused_inputs(p, &defs);
        }
        plan
    }

    fn omit_unused_inputs(&mut self, p: &Program, defs: &[Option<&Op>]) {
        // Only remove producers whose last use disappeared in a replaced
        // expression. An input used at another site or exit must still exist.
        let mut uses = p.use_counts();
        let mut removed = Vec::new();
        for (&root, rotate) in &self.roots {
            uses[rotate.value.index()] += 1;
            if let Count::Register(count) = rotate.count {
                uses[count.index()] += 1;
            }
            removed.extend(p.operands(defs[root.index()].unwrap()));
        }
        while let Some(value) = removed.pop() {
            uses[value.index()] -= 1;
            if uses[value.index()] == 0
                && let Some(op) = defs[value.index()]
            {
                // The only newly dead intermediates in a matched expression.
                if matches!(
                    op,
                    Op::Constant { .. }
                        | Op::Convert { .. }
                        | Op::Shift { .. }
                        | Op::Binary {
                            op: Binary::Mul | Binary::ShiftUp,
                            ..
                        }
                ) {
                    self.omitted.insert(value);
                    removed.extend(p.operands(op));
                }
            }
        }
    }
}

struct Shapes<'a> {
    p: &'a Program,
    defs: &'a [Option<&'a Op>],
}

impl Shapes<'_> {
    fn op(&self, value: ValueId) -> Option<Op> {
        self.defs[value.index()].copied()
    }

    fn bits(&self, value: ValueId) -> u16 {
        self.p.class(value).bits(WORD_BITS)
    }

    /// A right shift, optionally narrowed only far enough to discard zeros.
    fn high_part(&self, high: ValueId) -> Option<(ValueId, u16)> {
        let (high_shift, kept) = match self.op(high) {
            Some(Op::Convert { value }) => (value, self.bits(high)),
            _ => (high, WORD_BITS),
        };
        let Op::Shift {
            direction: Direction::Down,
            value: moved,
            by,
        } = self.op(high_shift)?
        else {
            return None;
        };
        (kept >= self.bits(moved).saturating_sub(by)).then_some((moved, by))
    }

    /// Match `low_w(x << n) + ((x << n) >> w)` or complementary shifts
    /// of the input. The parts have disjoint bits, so XOR and OR agree.
    fn join(&self, low: ValueId, high: ValueId) -> Option<Rotate> {
        let (moved, by) = self.high_part(high)?;
        let (low_shift, bits) = match self.op(low)? {
            Op::Convert { value } => (value, self.bits(low)),
            // A 64-bit left shift already drops the bits above the word.
            Op::Shift {
                direction: Direction::Up,
                ..
            } if self.bits(low) == 64 => (low, 64),
            _ => return None,
        };
        if !matches!(bits, 8 | 16 | 32 | 64) {
            return None;
        }
        let (value, count) = self.shifted(low_shift)?;
        if self.bits(value) > bits {
            return None;
        }
        if by == bits && bits < WORD_BITS {
            if self.shifted(moved)? != (value, count) {
                return None;
            }
        } else if !(moved == value
            && matches!(count, Count::Immediate(n) if bits.checked_sub(u16::from(n)) == Some(by)))
        {
            return None;
        }
        // A boundary may transmit any value fitting its class width, even
        // where its inferred range has a tighter upper endpoint.
        let bounded = match count {
            Count::Immediate(n) => u16::from(n) < bits,
            Count::Register(n) => self.bits(n) <= u16::try_from(bits.ilog2()).ok()?,
        };
        bounded.then_some(Rotate { value, bits, count })
    }

    fn shifted(&self, shifted: ValueId) -> Option<(ValueId, Count)> {
        match self.op(shifted)? {
            Op::Shift {
                direction: Direction::Up,
                value,
                by,
            } => Some((value, Count::Immediate(u8::try_from(by).ok()?))),
            Op::Binary {
                op: Binary::ShiftUp,
                left,
                right,
            } => Some((left, Count::Register(right))),
            Op::Binary {
                op: Binary::Mul,
                left,
                right,
            } => self
                .scaled(left, right)
                .or_else(|| self.scaled(right, left)),
            _ => None,
        }
    }

    fn scaled(&self, value: ValueId, power: ValueId) -> Option<(ValueId, Count)> {
        let Op::Binary {
            op: Binary::ShiftUp,
            left,
            right,
        } = self.op(power)?
        else {
            return None;
        };
        matches!(self.op(left), Some(Op::Constant { value: 1 }))
            .then_some((value, Count::Register(right)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Class;

    #[test]
    fn recognition_requires_matching_halves_and_preserves_other_uses() {
        let byte = Class::fixed(8);
        let wide = Class::fixed(16);
        // A count above 7 cannot rotate a byte in this expression. With
        // x = 1 and n = 9 its two parts sum to 2, but x = 255 yields 510.
        let (mut p, main) = Program::new_with_params(
            "main",
            &[
                ("x", byte),
                ("y", byte),
                ("n", Class::fixed(3)),
                ("m", Class::fixed(3)),
                ("larger", Class::fixed(4)),
            ],
        );
        let mut joins = Vec::new();
        let mut shared = None;
        p.define(main, |b, a| {
            let moved = b.binary_at(wide, Binary::ShiftUp, a[0], a[2]);
            let low = b.convert(byte, moved);
            let high = b.shift(wide, Direction::Down, moved, 8);
            for op in [Binary::Add, Binary::Or, Binary::Xor] {
                joins.push(b.binary_at(wide, op, high, low));
            }
            for (input, count) in [(a[1], a[2]), (a[0], a[3])] {
                let other = b.binary_at(wide, Binary::ShiftUp, input, count);
                let other_high = b.shift(wide, Direction::Down, other, 8);
                joins.push(b.binary_at(wide, Binary::Add, low, other_high));
            }
            let clipped = b.convert(Class::fixed(3), high);
            joins.push(b.binary_at(wide, Binary::Add, low, clipped));
            let large = b.binary_at(Class::fixed(32), Binary::ShiftUp, a[0], a[4]);
            let low_large = b.convert(byte, large);
            let high_large = b.shift(Class::fixed(32), Direction::Down, large, 8);
            joins.push(b.binary_at(Class::fixed(32), Binary::Add, low_large, high_large));
            shared = Some(moved);
            b.ret(&[moved]);
        });
        let plan = Plan::new(&p);
        for (at, result) in joins.iter().enumerate() {
            assert_eq!(plan.roots.contains_key(result), at < 3);
        }
        assert!(!plan.omitted.contains(&shared.unwrap()));
    }
}
