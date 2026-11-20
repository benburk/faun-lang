//! What a bound on an operation's answer says of its operands.
//!
//! A guard narrows what it compares: `n >= 2.pow(high)` holding says the
//! power is at most `n`. The power is worked out from `high`, so a bound on
//! it is a bound on `high` too, `high <= log2(n)`; and a quotient below `k`
//! says its dividend is below `k` times the divisor. An octagon relates
//! sums and differences, but a product, a quotient, a remainder or a power
//! is opaque to it, so this narrows their operands by intervals alone,
//! wherever an answer is narrowed (`notes/machine/ranges.md`).
//!
//! Each rule answers, given the answer `r = a op b` lies within `held` and
//! its operands within `a` and `b`, intervals each operand must lie within
//! for that to be so. A rule may give back what it was given; it must
//! never give less than every operand value for which the answer is in
//! `held`, since a bound too narrow compiles a word that can overflow.

use super::facts::Operation;
use crate::Bounds;

/// The naturals from `low` to `high`, a greatest past `u64` being no
/// bound; nothing where the least is past the greatest.
fn between(low: u128, high: Option<u128>) -> Bounds {
    let bounds = Bounds {
        low: u64::try_from(low).unwrap_or(u64::MAX),
        high: high.and_then(|high| u64::try_from(high).ok()),
    };
    if bounds.is_nothing() || high.is_some_and(|high| high < low) {
        Bounds::NOTHING
    } else {
        bounds
    }
}

fn high(bounds: Bounds) -> Option<u128> {
    bounds.high.map(u128::from)
}

fn low(bounds: Bounds) -> u128 {
    u128::from(bounds.low)
}

/// The greatest `e` with `base^e <= n`, for `base >= 2`.
const fn log_floor(base: u128, n: u128) -> u128 {
    let (mut power, mut exponent) = (1u128, 0u128);
    while let Some(next) = power.checked_mul(base) {
        if next > n {
            break;
        }
        power = next;
        exponent += 1;
    }
    exponent
}

/// The least `e` with `base^e >= n`, for `base >= 2`.
const fn log_ceiling(base: u128, n: u128) -> u128 {
    let (mut power, mut exponent) = (1u128, 0u128);
    while power < n {
        match power.checked_mul(base) {
            Some(next) => power = next,
            None => return exponent + 1,
        }
        exponent += 1;
    }
    exponent
}

/// Intervals `a` and `b` lie within where `a op b` lies within `held`, or
/// nothing where no rule says anything.
#[expect(
    clippy::too_many_lines,
    reason = "one rule for each operation, each short"
)]
pub(super) fn operands(
    op: Operation,
    held: Bounds,
    (a, b): (Bounds, Bounds),
) -> Option<(Bounds, Bounds)> {
    if held.is_nothing() || a.is_nothing() || b.is_nothing() {
        return None;
    }
    let (rl, rh) = (low(held), high(held));
    match op {
        // `r = a + b`: `a = r - b`.
        Operation::Add => Some((
            between(
                rl.saturating_sub(high(b).unwrap_or(u128::MAX)),
                rh.map(|rh| rh.saturating_sub(low(b))),
            ),
            between(
                rl.saturating_sub(high(a).unwrap_or(u128::MAX)),
                rh.map(|rh| rh.saturating_sub(low(a))),
            ),
        )),
        // `r = max(a - b, 0)`: `a <= r + b` always, `b >= a - r` always;
        // and where `r >= 1`, `a = r + b` exactly.
        Operation::Monus => {
            let a_high = rh.zip(high(b)).map(|(rh, bh)| rh + bh);
            let b_low = low(a).saturating_sub(rh.unwrap_or(u128::MAX));
            if rl >= 1 {
                Some((
                    between(rl + low(b), a_high),
                    between(b_low, high(a).map(|ah| ah.saturating_sub(rl))),
                ))
            } else {
                Some((between(0, a_high), between(b_low, None)))
            }
        }
        // `r = a * b`. Where `r >= 1`, neither is nought. Where the other
        // is at least `m`, this one is at most `r / m`; where the other is
        // at most `m`, this one is at least `r / m`, rounded up.
        Operation::Mul => {
            let side = |other: Bounds| -> Bounds {
                let least = if rl >= 1 {
                    high(other).map_or(1, |most| {
                        if most == 0 {
                            u128::MAX
                        } else {
                            rl.div_ceil(most).max(1)
                        }
                    })
                } else {
                    0
                };
                let most = (other.low >= 1)
                    .then(|| rh.map(|rh| rh / low(other)))
                    .flatten();
                between(least, most)
            };
            Some((side(b), side(a)))
        }
        // `r = a / b`, nought where `b` is. Where `r >= 1`, `b >= 1`; then
        // `r * b <= a < (r + 1) * b`, so `a` lies within `r` times `b`'s
        // least and one less than `r + 1` times its most.
        Operation::Div => {
            let b_least = u128::from(rl >= 1);
            if b.low == 0 && rl == 0 {
                return Some((Bounds::ANY, Bounds::ANY));
            }
            let a_least = rl.saturating_mul(low(b).max(b_least));
            let a_most = rh
                .zip(high(b))
                .and_then(|(rh, bh)| (rh + 1).checked_mul(bh))
                .map(|most| most - 1);
            // Where `b` may be nought the quotient is nought, which says
            // nothing of `a` but where `r >= 1` rules it out.
            let a_most = if b.low == 0 && rl == 0 { None } else { a_most };
            // `b <= a / r` where `r >= 1`.
            let b_most = if rl >= 1 {
                high(a).map(|ah| ah / rl)
            } else {
                None
            };
            Some((between(a_least, a_most), between(b_least, b_most)))
        }
        // `r = a % b`, `a` where `b` is nought: `r <= a` always, and where
        // `b >= 1`, `b > r`.
        Operation::Mod => {
            let b_least = if b.low >= 1 { rl + 1 } else { 0 };
            Some((between(rl, None), between(b_least, None)))
        }
        // `r = a & b <= each`, and `r = a | b >= each`.
        Operation::And => Some((between(rl, None), between(rl, None))),
        Operation::Or => Some((between(0, rh), between(0, rh))),
        // `r = a ^ b`, one where `b` is nought. With `a >= 2`, `a^b` grows
        // with `b`, so `b` lies between the logs of `r`'s bounds by `a`'s
        // most and least; with `b >= 1`, `a <= r`.
        Operation::Pow => {
            let exponent = if a.low >= 2 {
                let most = rh.map(|rh| log_floor(low(a), rh));
                let least = high(a).map_or(0, |ah| if rl <= 1 { 0 } else { log_ceiling(ah, rl) });
                between(least, most)
            } else {
                Bounds::ANY
            };
            let base = if b.low >= 1 {
                between(0, rh)
            } else {
                Bounds::ANY
            };
            Some((base, exponent))
        }
        Operation::Xor | Operation::Equals { .. } | Operation::LessThan { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::*;
    use crate::CtorId;

    fn contains(bounds: Bounds, value: &BigUint) -> bool {
        BigUint::from(bounds.low) <= *value
            && bounds.high.is_none_or(|high| *value <= BigUint::from(high))
    }

    /// Values at the edges: nought, one, powers of two and their
    /// neighbours, near the most a `u64` holds, and past it.
    fn edges() -> Vec<BigUint> {
        let mut values: Vec<BigUint> = (0u64..=20).map(BigUint::from).collect();
        for shift in [7u32, 8, 15, 16, 31, 32, 52, 53, 62, 63] {
            let power = BigUint::from(1u8) << shift;
            values.extend([power.clone() - 1u8, power.clone(), power.clone() + 1u8]);
        }
        let most = BigUint::from(u64::MAX);
        values.extend([
            most.clone() - 1u8,
            most.clone(),
            most.clone() + 1u8,
            most * 3u8,
        ]);
        values
    }

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self, below: usize) -> usize {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            usize::try_from(self.0 >> 33).unwrap() % below
        }
    }

    /// An interval with ends drawn from `values`, the greatest sometimes
    /// none.
    fn interval(random: &mut Lcg, values: &[BigUint]) -> Bounds {
        let as_u64 = |value: &BigUint| u64::try_from(value).unwrap_or(u64::MAX);
        let (first, second) = (
            &values[random.next(values.len())],
            &values[random.next(values.len())],
        );
        let (low, high) = if first <= second {
            (first, second)
        } else {
            (second, first)
        };
        let high = if random.next(5) == 0 || u64::try_from(high).is_err() {
            None
        } else {
            Some(as_u64(high))
        };
        Bounds {
            low: as_u64(low).min(high.unwrap_or(u64::MAX)),
            high,
        }
    }

    /// For every operation, operands drawn from the edges and intervals
    /// drawn round them: wherever the answer lies in the answer's interval,
    /// each operand lies in what the rule narrowed it to.
    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "drawing operands, intervals and answers, and checking each"
    )]
    fn narrowing_an_answer_keeps_every_operand_that_reaches_it() {
        let (yes, no) = (CtorId::at(1), CtorId::at(0));
        let operations = [
            Operation::Add,
            Operation::Monus,
            Operation::Mul,
            Operation::Div,
            Operation::Mod,
            Operation::And,
            Operation::Or,
            Operation::Pow,
            Operation::Xor,
            Operation::LessThan { yes, no },
        ];
        let values = edges();
        let mut random = Lcg(17);
        let mut checked = 0;
        for _ in 0..1200 {
            let op = operations[random.next(operations.len())];
            let (a, b, held) = (
                interval(&mut random, &values),
                interval(&mut random, &values),
                interval(&mut random, &values),
            );
            let Some((narrow_a, narrow_b)) = operands(op, held, (a, b)) else {
                continue;
            };
            for x in values.iter().filter(|x| contains(a, x)) {
                for y in values.iter().filter(|y| contains(b, y)) {
                    // A power past what `calculate` works out is past any
                    // bound too.
                    let Some(answer) = op.calculate(x, y) else {
                        continue;
                    };
                    if !contains(held, &answer) {
                        continue;
                    }
                    checked += 1;
                    assert!(
                        contains(narrow_a, x) && contains(narrow_b, y),
                        "{op:?} {x} {y} = {answer} in {held:?}: {a:?} {b:?} narrowed to {narrow_a:?} {narrow_b:?}"
                    );
                }
            }
        }
        assert!(checked > 3_000, "{checked}");
    }

    #[test]
    fn a_power_bounds_its_exponent() {
        let two = Bounds::at(2);
        let held = Bounds {
            low: 0,
            high: Some(1 << 20),
        };
        let (_, exponent) = operands(Operation::Pow, held, (two, Bounds::ANY)).unwrap();
        assert_eq!(exponent.high, Some(20));
        // A base of nought or one says nothing of its exponent.
        let small = Bounds {
            low: 0,
            high: Some(1),
        };
        let (_, exponent) = operands(Operation::Pow, held, (small, Bounds::ANY)).unwrap();
        assert_eq!(exponent, Bounds::ANY);
    }

    #[test]
    fn a_product_bounds_a_factor_by_the_other() {
        let held = Bounds {
            low: 0,
            high: Some(99),
        };
        let (x, _) = operands(Operation::Mul, held, (Bounds::ANY, Bounds::at(8))).unwrap();
        assert_eq!(x.high, Some(12));
        // A factor that may be nought bounds nothing.
        let (x, _) = operands(
            Operation::Mul,
            held,
            (
                Bounds::ANY,
                Bounds {
                    low: 0,
                    high: Some(8),
                },
            ),
        )
        .unwrap();
        assert_eq!(x.high, None);
    }

    #[test]
    fn a_quotient_bounds_its_dividend() {
        let held = Bounds {
            low: 0,
            high: Some(9),
        };
        let (x, _) = operands(Operation::Div, held, (Bounds::ANY, Bounds::at(8))).unwrap();
        assert_eq!(x.high, Some(79));
    }

    #[test]
    fn a_difference_of_nought_bounds_the_first_by_the_second() {
        let (a, _) = operands(
            Operation::Monus,
            Bounds::at(0),
            (
                Bounds::ANY,
                Bounds {
                    low: 0,
                    high: Some(40),
                },
            ),
        )
        .unwrap();
        assert_eq!(a.high, Some(40));
        let (a, b) = operands(
            Operation::Monus,
            Bounds { low: 3, high: None },
            (
                Bounds::ANY,
                Bounds {
                    low: 5,
                    high: Some(40),
                },
            ),
        )
        .unwrap();
        assert_eq!((a.low, b.low), (8, 0));
    }
}
