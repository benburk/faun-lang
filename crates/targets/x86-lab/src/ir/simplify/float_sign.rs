//! Recognize the sign of a difference after NaN canonicalization. Matching
//! the observation matters: a raw NaN bit pattern can have either sign.
use super::{Exit, Format, Op, Operation, Program, RegionId, Relation, ValueId, Wrote};

impl Wrote {
    fn yielded(p: &Program, region: RegionId) -> Option<ValueId> {
        let end = p.region(region).terminator?;
        let &[value] = p.values(end.values) else {
            return None;
        };
        (end.exit == Exit::Yield).then_some(value)
    }

    fn choice(&self, p: &Program, value: ValueId) -> Option<(ValueId, ValueId, ValueId)> {
        let Op::If {
            condition,
            then_region,
            else_region,
        } = self.0[value.index()]?.0
        else {
            return None;
        };
        Some((
            condition,
            Self::yielded(p, then_region)?,
            Self::yielded(p, else_region)?,
        ))
    }

    fn comparison(&self, value: ValueId, expected: Relation) -> Option<(ValueId, ValueId)> {
        let Op::Compare {
            relation,
            left,
            right,
        } = self.0[value.index()]?.0
        else {
            return None;
        };
        (relation == expected).then_some((left, right))
    }

    /// The standard observation returns the original bits for magnitudes
    /// below or equal to infinity, and a positive NaN for larger magnitudes.
    fn observed(&self, p: &Program, value: ValueId, bits: u16, infinity: u64) -> Option<ValueId> {
        let (keep, raw, nan) = self.choice(p, value)?;
        if self.number(nan)? >> (bits - 1) != 0 {
            return None;
        }
        let (is_nan, zero) = self.comparison(keep, Relation::Equal)?;
        let (below, finite, at_limit) = self.choice(p, is_nan)?;
        let (mag, limit) = self.comparison(below, Relation::Less)?;
        let (equal, at_infinity, above) = self.choice(p, at_limit)?;
        if self.comparison(equal, Relation::Equal)? != (mag, limit)
            || self.number(limit)? != infinity
            || self.number(zero)? != 0
            || self.number(finite)? != 0
            || self.number(at_infinity)? != 0
            || self.number(above)? == 0
        {
            return None;
        }
        let Op::Convert { value: original } = self.0[mag.index()]?.0 else {
            return None;
        };
        (original == raw && p.class(mag).width() == Some(bits - 1)).then_some(raw)
    }

    pub(super) fn nonnegative_difference(
        &self,
        p: &Program,
        seen: ValueId,
        sign: ValueId,
    ) -> Option<(Format, ValueId, ValueId)> {
        let sign_bit = self.number(sign)?;
        let (format, infinity) = match sign_bit {
            0x8000_0000 => (Format::Binary32, 0x7f80_0000),
            0x8000_0000_0000_0000 => (Format::Binary64, 0x7ff0_0000_0000_0000),
            _ => return None,
        };
        let raw = self.observed(p, seen, format.bits(), infinity)?;
        let Op::Float { float, operands } = self.0[raw.index()]?.0 else {
            return None;
        };
        if float.format != format || float.operation != Operation::Sub {
            return None;
        }
        let &[a, b] = p.values(operands) else {
            return None;
        };
        // With round-to-nearest and gradual underflow, two distinct finite
        // operands differ by at least one subnormal. Only -0 minus +0 yields
        // a negative zero. Exclude that pair before using an ordered compare.
        if self.number(a).is_some_and(|n| n != sign_bit) || self.number(b).is_some_and(|n| n != 0) {
            Some((format, a, b))
        } else {
            None
        }
    }
}
