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

use super::{Builder, Class, Exit, Op, Program, RegionId, ValueId, model::wrap, rewrite};

/// Rebuild `source` with those shapes read as what they mean.
///
/// What stops being read is left where it stands; [`super::prune`] is what
/// takes it away.
#[must_use]
pub(super) fn simplify(source: &Program) -> Program {
    let mut pass = Simplify {
        wrote: Wrote::of(source),
    };
    rewrite::rebuild(source, &mut pass)
}

struct Simplify {
    wrote: Wrote,
}

impl rewrite::Pass for Simplify {
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        let source = rebuild.source();
        match op {
            // A constant read at another width is that constant, written at
            // the width it is read at. Only a `Fixed` sink is written here:
            // it says its own width, where a word's is the machine's and is
            // not something this tier knows.
            Op::Convert {
                class: class @ Class::Fixed { .. },
                value,
            } => {
                let Some(held) = self.wrote.number(value) else {
                    return false;
                };
                rebuild.stands_for(results[0], b.constant(class, wrap(class, held)));
                true
            }
            // A branch asking which constructor a comparison answered is the
            // comparison, and the arms stand in whichever order its tags say.
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                let Some((test, swapped)) = self.wrote.asks(source, condition) else {
                    return false;
                };
                let arms = if swapped {
                    (else_region, then_region)
                } else {
                    (then_region, else_region)
                };
                let test = rebuild.value(test);
                let fresh = rebuild.if_(b, test, results, arms.0, arms.1, self);
                for (&was, now) in results.iter().zip(fresh) {
                    rebuild.stands_for(was, now);
                }
                true
            }
            _ => false,
        }
    }
}

/// What wrote each value, which is what lets one instruction be read
/// together with the ones it reads.
struct Wrote(Vec<Option<Op>>);

impl Wrote {
    fn of(source: &Program) -> Self {
        let mut held = vec![None; source.values_count()];
        for function in source.functions() {
            let Some(body) = function.body() else {
                continue;
            };
            for (op, results) in every(source, body) {
                for value in results {
                    held[value.index()] = Some(op);
                }
            }
        }
        Self(held)
    }

    /// The number a value is, where a constant wrote it. A natural is held
    /// in the data pool rather than as a number here, and says nothing.
    fn number(&self, value: ValueId) -> Option<u64> {
        match self.0[value.index()]? {
            Op::Constant {
                class: Class::Word | Class::Fixed { .. },
                value,
            } => Some(value),
            _ => None,
        }
    }

    /// Whether a condition only asks which of two constants an earlier
    /// branch chose, and if so, that branch's own condition and whether the
    /// answer runs the arms the other way round.
    fn asks(&self, source: &Program, condition: ValueId) -> Option<(ValueId, bool)> {
        let Op::Compare {
            relation: super::Relation::Equal,
            left,
            right,
        } = self.0[condition.index()]?
        else {
            return None;
        };
        let wanted = self.number(right)?;
        let (test, taken, otherwise) = self.chose(source, left)?;
        // Nothing is decided by asking which of two of the same it was.
        if taken == otherwise {
            return None;
        }
        if wanted == taken {
            Some((test, false))
        } else if wanted == otherwise {
            Some((test, true))
        } else {
            None
        }
    }

    /// A branch whose arms do nothing but answer with a constant each: its
    /// condition, what it answers when the condition holds, and what it
    /// answers when it does not.
    fn chose(&self, source: &Program, value: ValueId) -> Option<(ValueId, u64, u64)> {
        let Op::If {
            condition,
            then_region,
            else_region,
        } = self.0[value.index()]?
        else {
            return None;
        };
        Some((
            condition,
            self.answered(source, then_region)?,
            self.answered(source, else_region)?,
        ))
    }

    /// The one constant an arm leaves with, where that is all the arm does.
    fn answered(&self, source: &Program, region: RegionId) -> Option<u64> {
        let terminator = source.region(region).terminator?;
        if terminator.exit != Exit::Yield || source.ops(region).len() != 1 {
            return None;
        }
        let &[value] = source.values(terminator.values) else {
            return None;
        };
        self.number(value)
    }
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
