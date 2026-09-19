//! Portable legalization of natural arithmetic. Backends can later replace
//! these regions with native multiply/divide or bigint runtime calls.

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

fn at(b: &mut Builder, value: ValueId, class: Class) -> ValueId {
    if b.class(value) == class {
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
    let answer = match op {
        Operation::Add => b.binary(Binary::Add, left, right),
        Operation::Monus => monus(b, class, left, right),
        Operation::Mul => multiply(b, class, left, right),
        Operation::Div | Operation::Mod => divide(b, class, left, right, op == Operation::Mod),
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
            b.yield_(&[zero])
        },
        |b| {
            let value = b.binary(Binary::Sub, left, right);
            b.yield_(&[value])
        },
    )[0]
}

fn multiply(b: &mut Builder, class: Class, left: ValueId, right: ValueId) -> ValueId {
    let zero = b.constant(class, 0);
    b.loop_(&[right, zero], &[class], |b, state| {
        let done = b.compare(Relation::Equal, state[0], zero);
        b.if_(
            done,
            &[],
            |b| b.break_(&[state[1]]),
            |b| {
                let one = b.constant(class, 1);
                let rest = b.binary(Binary::Sub, state[0], one);
                let sum = b.binary(Binary::Add, state[1], left);
                b.continue_(&[rest, sum])
            },
        );
        super::Terminator::UNREACHABLE
    })[0]
}

fn divide(
    b: &mut Builder,
    class: Class,
    left: ValueId,
    right: ValueId,
    remainder: bool,
) -> ValueId {
    let zero = b.constant(class, 0);
    let is_zero = b.compare(Relation::Equal, right, zero);
    b.if_(
        is_zero,
        &[class],
        |b| b.yield_(&[if remainder { left } else { zero }]),
        |b| {
            let answer = b.loop_(&[left, zero], &[class], |b, state| {
                let done = b.compare(Relation::Less, state[0], right);
                b.if_(
                    done,
                    &[],
                    |b| b.break_(&[if remainder { state[0] } else { state[1] }]),
                    |b| {
                        let remainder = b.binary(Binary::Sub, state[0], right);
                        let one = b.constant(class, 1);
                        let quotient = b.binary(Binary::Add, state[1], one);
                        b.continue_(&[remainder, quotient])
                    },
                );
                super::Terminator::UNREACHABLE
            });
            b.yield_(&answer)
        },
    )[0]
}
