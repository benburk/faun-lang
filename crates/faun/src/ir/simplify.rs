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
//! And the same for a run of them. A number one past another is a
//! constructor where a program is written, and the tier above has no
//! addition to fold four of those into; this one does, so four steps of one
//! are a step of four.

use super::{Binary, Builder, Class, Exit, Op, Program, RegionId, ValueId, model::wrap, rewrite};

/// Rebuild `source` with those shapes read as what they mean.
///
/// What stops being read is left where it stands; [`super::prune`] is what
/// takes it away.
#[must_use]
pub(super) fn simplify(source: &Program) -> Program {
    let mut pass = Simplify {
        wrote: Wrote::of(source),
        steps: vec![None; source.values_count()],
    };
    rewrite::rebuild(source, &mut pass)
}

struct Simplify {
    wrote: Wrote,
    /// What each old value is a fixed step past, once anything has been
    /// found to be a step past anything. Written as the walk goes, since
    /// what a step is past is whatever the walk has already written.
    steps: Vec<Option<Step>>,
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
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        match op {
            Op::Convert { value } => {
                let class = rebuild.source().class(results[0]);
                matches!(class, Class::Held(_))
                    && self.widened(rebuild, b, class, value, results[0])
            }
            Op::Binary {
                op: Binary::Add,
                left,
                right,
            } => self.stepping(rebuild, b, left, right, results[0]),
            Op::If {
                condition,
                then_region,
                else_region,
            } => self.branching(rebuild, b, condition, [then_region, else_region], results),
            _ => false,
        }
    }
}

impl Simplify {
    /// A constant read at another width is that constant, written at the
    /// width it is read at.
    ///
    /// Only a `Fixed` sink is written here: it says its own width, where a
    /// word's is the machine's and is not something this tier knows.
    fn widened(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        class: Class,
        value: ValueId,
        result: ValueId,
    ) -> bool {
        let Some(held) = self.wrote.number(value) else {
            return false;
        };
        rebuild.stands_for(result, b.constant(class, wrap(class, held)));
        true
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
        let by = b.constant(class, step.by);
        let from = rebuild.value(step.from);
        rebuild.stands_for(result, b.binary_at(class, Binary::Add, from, by));
        true
    }

    /// A branch asking which constructor a comparison answered is the
    /// comparison, with its arms in whichever order the tags say.
    fn branching(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        condition: ValueId,
        arms: [RegionId; 2],
        results: &[ValueId],
    ) -> bool {
        let Some((test, swapped)) = self.wrote.asks(rebuild.source(), condition) else {
            return false;
        };
        let [then_region, else_region] = if swapped { [arms[1], arms[0]] } else { arms };
        let test = rebuild.value(test);
        let fresh = rebuild.if_(b, test, results, then_region, else_region, self);
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
        let by = self.wrote.number(right)?;
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

/// What wrote each value, which is what lets one instruction be read
/// together with the ones it reads.
struct Wrote(Vec<Option<(Op, Class)>>);

impl Wrote {
    fn of(source: &Program) -> Self {
        let mut held = vec![None; source.values_count()];
        for function in source.functions() {
            let Some(body) = function.body() else {
                continue;
            };
            for (op, results) in every(source, body) {
                for value in results {
                    held[value.index()] = Some((op, source.class(value)));
                }
            }
        }
        Self(held)
    }

    /// The number a value is, where a constant wrote it. A natural is held
    /// in the data pool rather than as a number here, and says nothing.
    fn number(&self, value: ValueId) -> Option<u64> {
        let (op, class) = self.0[value.index()]?;
        match op {
            Op::Constant { value } if matches!(class, Class::Word | Class::Held(_)) => Some(value),
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
        } = self.0[condition.index()]?.0
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
        } = self.0[value.index()]?.0
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
