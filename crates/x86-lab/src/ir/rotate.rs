//! Loops tested where they go round rather than where they begin.
//!
//! A loop lowering writes asks whether it is done first, every time round:
//!
//! ```text
//! loop(p):                          h = header(p)
//!   h = header(p)                   if done(h) then answer(p, h)
//!   if done(h) then answer(p, h)    else loop(p):
//!   else step(p); continue(n)              step(p)
//!                                           h' = header(n)
//!                                           if done(h') then break answer(n, h')
//!                                           else continue(n)
//! ```
//!
//! Written the second way it asks the same questions in the same order, but
//! where it goes round: a machine then jumps back only when it does, rather
//! than jumping back to ask and over the answer to go on. The header runs as
//! often as before, once before the first time round and once at the end of
//! each; the step may read only its constants, written again where the step
//! begins, so what goes round is what went round before. The answer is written twice, so only a loop whose
//! header and answer hold no regions, and whose answer is a few
//! instructions, is written again.

use super::rewrite::{self, Pass, Rebuild};
use super::{Builder, Exit, Op, Program, RegionId, Terminator, ValueId};

/// The most instructions an answer written twice may hold.
const ANSWER: usize = 4;
/// The most instructions a header written twice may hold.
const HEADER: usize = 8;

/// Rewrite every loop of that shape in `source`.
#[must_use]
pub fn rotate(source: &Program) -> Program {
    rewrite::rebuild(source, &mut Rotate::default())
}

/// A loop's body read as a header, a question, an answer and a step.
#[derive(Clone)]
struct Shape {
    params: Vec<ValueId>,
    header: Vec<(Op, Vec<ValueId>)>,
    condition: ValueId,
    /// The arm answering, and the arm going round.
    answer: RegionId,
    step: RegionId,
    answer_first: bool,
    /// The header's constants the step reads, written again where it
    /// begins: anything else of the header it reads would have to go round
    /// with it, which a machine with few registers to carry a loop in may
    /// not have room for.
    constants: Vec<(Op, Vec<ValueId>)>,
}

/// Each loop being written again, by how deep it is, and how deep the walk
/// is in loops.
#[derive(Default)]
struct Rotate {
    rotating: Vec<(usize, Shape)>,
    depth: usize,
}

impl Pass for Rotate {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let Op::Loop { initial, body } = op else {
            return false;
        };
        self.depth += 1;
        match shape(rebuild.source(), body) {
            Some(shape) => {
                let initial = rebuild.args(initial);
                let fresh = self.rotated(rebuild, b, &shape, &initial, results);
                for (&was, now) in results.iter().zip(fresh) {
                    rebuild.stands_for(was, now);
                }
            }
            None => rebuild.copy(b, op, results, self),
        }
        self.depth -= 1;
        true
    }

    fn exit(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, terminator: Terminator) -> bool {
        let Some((depth, shape)) = self.rotating.last() else {
            return false;
        };
        if terminator.exit != Exit::Continue || *depth != self.depth {
            return false;
        }
        let shape = shape.clone();
        let next = rebuild.args(terminator.values);
        self.bottom(rebuild, b, &shape, &next);
        true
    }
}

impl Rotate {
    /// Where the step goes round with `next`: the header and question
    /// again, then the answer, leaving, or going round.
    fn bottom(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, shape: &Shape, next: &[ValueId]) {
        // What the header and the answer read is what goes round, here; the
        // rest of the step, written before or after, reads what came in.
        let saved: Vec<_> = shape
            .params
            .iter()
            .chain(shape.header.iter().flat_map(|(_, results)| results))
            .map(|&old| (old, rebuild.standing(old)))
            .collect();
        for (&param, &now) in shape.params.iter().zip(next) {
            rebuild.stands_for(param, now);
        }
        for (op, results) in &shape.header {
            rebuild.copy(b, *op, results, self);
        }
        let condition = rebuild.value(shape.condition);
        let source = rebuild.source();
        let answer = source.region(shape.answer);
        let done = |b: &mut Builder| {
            for (op, results) in source.walk(shape.answer) {
                rebuild.copy(b, *op, results, &mut Self::default());
            }
            let values = answer
                .terminator
                .map_or_else(Vec::new, |exit| rebuild.args(exit.values));
            b.break_(&values);
        };
        let round = |b: &mut Builder| b.continue_(next);
        if shape.answer_first {
            b.if_(condition, &[], done, round);
        } else {
            b.if_(condition, &[], round, done);
        }
        for (old, standing) in saved {
            rebuild.restand(old, standing);
        }
    }

    /// The loop `shape` describes, started with `initial`: its header and
    /// question once, then the answer, or the loop going round with its
    /// question at the end. What it answers.
    fn rotated(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        shape: &Shape,
        initial: &[ValueId],
        results: &[ValueId],
    ) -> Vec<ValueId> {
        let initial = at_classes(rebuild.source(), b, initial, &shape.params);
        for (&param, &now) in shape.params.iter().zip(&initial) {
            rebuild.stands_for(param, now);
        }
        for (op, results) in &shape.header {
            rebuild.copy(b, *op, results, self);
        }
        let condition = rebuild.value(shape.condition);
        let classes = rebuild.classes(results);
        // What the guard worked out, which an arm built after the loop reads.
        let guard: Vec<_> = shape
            .params
            .iter()
            .chain(shape.header.iter().flat_map(|(_, results)| results))
            .map(|&old| (old, rebuild.standing(old)))
            .collect();
        let pass = std::cell::RefCell::new(self);
        let answer = |b: &mut Builder| {
            let mut pass = pass.borrow_mut();
            rebuild.region(b, shape.answer, &[], &mut **pass);
        };
        let round = |b: &mut Builder| {
            let mut pass = pass.borrow_mut();
            let answered = pass.going_round(rebuild, b, shape, (&initial, &classes));
            for &(old, standing) in &guard {
                rebuild.restand(old, standing);
            }
            b.yield_(&answered);
        };
        if shape.answer_first {
            b.if_(condition, &classes, answer, round)
        } else {
            b.if_(condition, &classes, round, answer)
        }
    }

    /// The loop going round from `initial`, answering at `classes`: the
    /// header's constants the step reads, then the step, whose going round
    /// [`Self::bottom`] writes.
    fn going_round(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        shape: &Shape,
        (initial, classes): (&[ValueId], &[super::Class]),
    ) -> Vec<ValueId> {
        b.loop_(initial, classes, |b, params| {
            for (&param, &value) in shape.params.iter().zip(params) {
                rebuild.stands_for(param, value);
            }
            for (op, results) in &shape.constants {
                rebuild.copy(b, *op, results, self);
            }
            self.rotating.push((self.depth, shape.clone()));
            rebuild.region(b, shape.step, &[], self);
            self.rotating.pop();
        })
    }
}

/// `values`, each at the class of the parameter it starts: a loop goes round
/// at the classes it was written with, however much narrower what now
/// starts it is.
fn at_classes(
    source: &Program,
    b: &mut Builder,
    values: &[ValueId],
    params: &[ValueId],
) -> Vec<ValueId> {
    values
        .iter()
        .zip(params)
        .map(|(&value, &param)| {
            let class = source.class(param);
            if b.class(value) == class {
                value
            } else {
                b.convert(class, value)
            }
        })
        .collect()
}

/// Whether `body` reads as a header of no regions, then a question whose
/// one arm answers in a few instructions and whose other goes round, the
/// loop leaving with what the answer gives: and if so, its parts.
fn shape(source: &Program, body: RegionId) -> Option<Shape> {
    let region = source.region(body);
    let ops: Vec<(Op, Vec<ValueId>)> = source
        .walk(body)
        .map(|(op, results)| (*op, results.to_vec()))
        .collect();
    let ((last, answered), header) = ops.split_last()?;
    let Op::If {
        condition,
        then_region,
        else_region,
    } = *last
    else {
        return None;
    };
    let leaves = region.terminator?;
    if leaves.exit != Exit::Break
        || source.values(leaves.values) != answered.as_slice()
        || header.len() > HEADER
        || header.iter().any(|(op, _)| holds_region(*op))
    {
        return None;
    }
    let (answer, step, answer_first) = arms(source, then_region, else_region)?;
    let constants = constants(source, header, step)?;
    Some(Shape {
        params: source.values(region.params).to_vec(),
        header: header.to_vec(),
        condition,
        answer,
        step,
        answer_first,
        constants,
    })
}

/// Which of an `if`'s arms answers -- a few instructions holding no
/// region, then a yield -- and which goes round, never yielding; and
/// whether the answer is the first.
fn arms(
    source: &Program,
    then_region: RegionId,
    else_region: RegionId,
) -> Option<(RegionId, RegionId, bool)> {
    let answers = |arm: RegionId| {
        let region = source.region(arm);
        region
            .terminator
            .is_some_and(|exit| exit.exit == Exit::Yield)
            && region.ops.len() <= ANSWER
            && source.walk(arm).all(|(op, _)| !holds_region(*op))
    };
    let goes_round = |arm: RegionId| {
        source
            .region(arm)
            .terminator
            .is_none_or(|exit| exit.exit != Exit::Yield)
    };
    if answers(then_region) && goes_round(else_region) {
        Some((then_region, else_region, true))
    } else if answers(else_region) && goes_round(then_region) {
        Some((else_region, then_region, false))
    } else {
        None
    }
}

/// The header's constants `step` reads, where it reads nothing else the
/// header works out.
fn constants(
    source: &Program,
    header: &[(Op, Vec<ValueId>)],
    step: RegionId,
) -> Option<Vec<(Op, Vec<ValueId>)>> {
    let mut constants: Vec<(Op, Vec<ValueId>)> = Vec::new();
    for read in source
        .walk_within(step)
        .flat_map(|(op, _)| source.operands(op).collect::<Vec<_>>())
        .chain(within_exits(source, step))
    {
        let Some((op, results)) = header.iter().find(|(_, results)| results.contains(&read)) else {
            continue;
        };
        if !matches!(op, Op::Constant { .. }) {
            return None;
        }
        if !constants.iter().any(|(_, held)| held == results) {
            constants.push((*op, results.clone()));
        }
    }
    Some(constants)
}

/// What every region within `region`, and it, leaves with.
fn within_exits(source: &Program, region: RegionId) -> Vec<ValueId> {
    let mut regions = vec![region];
    let mut leaving = Vec::new();
    while let Some(region) = regions.pop() {
        leaving.extend_from_slice(source.outgoing(region));
        for (op, _) in source.walk(region) {
            match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => regions.extend([then_region, else_region]),
                Op::Loop { body, .. } => regions.push(body),
                _ => {}
            }
        }
    }
    leaving
}

const fn holds_region(op: Op) -> bool {
    matches!(op, Op::If { .. } | Op::Loop { .. })
}
