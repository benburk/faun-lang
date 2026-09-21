//! What the machine passes recognise, what they leave alone, and that a
//! program answers the same either way.
//!
//! Programs here are written straight into machine IR rather than read from
//! source, so each one says only the shape it is about. What lowering
//! actually writes is the frontend's business, and shown where it is read.

use num_bigint::BigUint;

use super::{
    Binary, Class, Op, OptimizeOptions, Program, Relation, Returns, ValueId, evaluate, optimize,
    validate,
};

const BIT: Class = Class::Fixed { bits: 1 };

/// A host that answers nothing, for programs that call nothing.
struct Silent;

impl evaluate::Host for Silent {
    fn call(
        &mut self,
        name: &str,
        _: &[BigUint],
        _: &mut evaluate::Memory<'_>,
    ) -> Result<evaluate::HostResult, evaluate::Error> {
        Err(evaluate::Error::Host(name.to_owned()))
    }
}

fn returns(p: &Program) -> BigUint {
    validate(p).expect("a sound program");
    evaluate::evaluate(p, p.entry(), &[], evaluate::Config::default(), &mut Silent)
        .expect("reference execution")
        .returned()
        .expect("a returning program")[0]
        .clone()
}

/// Optimized, having checked that it still answers what it answered.
fn settled(p: &Program) -> Program {
    let before = returns(p);
    let held = optimize(p, &OptimizeOptions::default());
    assert_eq!(returns(&held), before, "a pass changed what it answers");
    held
}

fn count(p: &Program, wanted: impl Fn(&Op) -> bool) -> usize {
    let body = p.function(p.entry()).body().expect("a body");
    p.every(body).filter(|op| wanted(op)).count()
}

const fn is_if(op: &Op) -> bool {
    matches!(*op, Op::If { .. })
}

/// The tag a comparison answers with, and a branch asking which tag it was:
/// what lowering writes when a match reads a comparison, and what the two
/// of them mean read together.
///
/// `tags` are what the comparison answers, true arm first.
fn tagged(tags: (u64, u64)) -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let three = b.constant(Class::Word, 3);
        let five = b.constant(Class::Word, 5);
        let test = b.compare(Relation::Less, three, five);
        let tag = b.if_(
            test,
            &[BIT],
            |b| {
                let held = b.constant(BIT, tags.0);
                b.yield_(&[held]);
            },
            |b| {
                let held = b.constant(BIT, tags.1);
                b.yield_(&[held]);
            },
        )[0];
        let nought = b.constant(BIT, 0);
        let asks = b.compare(Relation::Equal, tag, nought);
        let answer = arms(b, asks);
        b.ret(&[answer]);
    });
    p
}

/// Two arms answering two numbers, so which one ran can be read off the
/// program's own result.
fn arms(b: &mut super::Builder, condition: ValueId) -> ValueId {
    b.if_(
        condition,
        &[Class::Word],
        |b| {
            let held = b.constant(Class::Word, 10);
            b.yield_(&[held]);
        },
        |b| {
            let held = b.constant(Class::Word, 20);
            b.yield_(&[held]);
        },
    )[0]
}

#[test]
fn a_branch_asking_which_tag_a_comparison_answered_becomes_the_comparison() {
    let held = settled(&tagged((1, 0)));
    assert_eq!(count(&held, is_if), 1, "one branch, not two");
    assert_eq!(
        count(&held, |op| matches!(
            *op,
            Op::Compare {
                relation: Relation::Equal,
                ..
            }
        )),
        0,
        "nothing left asking which tag it was"
    );
    // 3 < 5, so the comparison holds, so the arm the `True` tag chose runs.
    assert_eq!(returns(&held), BigUint::from(20u8));
}

/// The tags say which arm is which, and a type may name its constructors
/// the other way round. Reading the comparison instead of the tag has to
/// keep them straight, which is the whole of what it must not get wrong.
#[test]
fn which_arm_a_fused_branch_runs_follows_the_tags() {
    for (tags, answer) in [((1, 0), 20u8), ((0, 1), 10)] {
        let held = settled(&tagged(tags));
        assert_eq!(count(&held, is_if), 1);
        assert_eq!(returns(&held), BigUint::from(answer), "tags {tags:?}");
    }
}

/// Two arms answering the same number say nothing about which one ran, so
/// asking which it was is not asking about the comparison.
#[test]
fn a_tag_that_says_nothing_is_not_read_as_a_comparison() {
    let held = settled(&tagged((1, 1)));
    assert_eq!(count(&held, is_if), 2, "neither branch is the other");
}

/// A tag something else reads is still worked out. Reading the comparison
/// at the branch takes nothing away from whoever wanted the number.
#[test]
fn a_tag_read_elsewhere_survives_the_branch_that_no_longer_needs_it() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let three = b.constant(Class::Word, 3);
        let five = b.constant(Class::Word, 5);
        let test = b.compare(Relation::Less, three, five);
        let tag = b.if_(
            test,
            &[BIT],
            |b| {
                let held = b.constant(BIT, 1);
                b.yield_(&[held]);
            },
            |b| {
                let held = b.constant(BIT, 0);
                b.yield_(&[held]);
            },
        )[0];
        let nought = b.constant(BIT, 0);
        let asks = b.compare(Relation::Equal, tag, nought);
        let answer = arms(b, asks);
        let held = b.convert(Class::Word, tag);
        let total = b.binary(Binary::Add, answer, held);
        b.ret(&[total]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, is_if), 2, "the tag is still worked out");
    assert_eq!(returns(&held), BigUint::from(21u8), "20, and the tag");
}

#[test]
fn a_constant_is_written_at_the_width_it_is_read_at() {
    let wide = Class::Fixed { bits: 9 };
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let narrow = b.constant(Class::Fixed { bits: 3 }, 5);
        let read = b.convert(wide, narrow);
        let other = b.constant(wide, 256);
        let total = b.binary(Binary::Add, read, other);
        let answer = b.convert(Class::Word, total);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    assert_eq!(
        count(
            &held,
            |op| matches!(*op, Op::Convert { class, .. } if class == wide)
        ),
        0,
        "the constant arrives wide rather than being widened"
    );
    assert_eq!(
        count(&held, |op| *op
            == Op::Constant {
                class: wide,
                value: 5
            }),
        1
    );
    assert_eq!(returns(&held), BigUint::from(261u16));
}

/// Read narrower, a constant is the number that fits, which is what writing
/// it at that width already means.
#[test]
fn a_constant_read_narrower_is_the_number_that_fits() {
    let narrow = Class::Fixed { bits: 3 };
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let wide = b.constant(Class::Fixed { bits: 9 }, 13);
        let read = b.convert(narrow, wide);
        let answer = b.convert(Class::Word, read);
        b.ret(&[answer]);
    });
    assert_eq!(
        returns(&settled(&p)),
        BigUint::from(5u8),
        "13 in three bits"
    );
}

#[test]
fn what_nothing_reads_goes_and_what_reads_it_keeps_it() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let kept = b.constant(Class::Word, 7);
        let dead = b.constant(Class::Word, 9);
        let also_dead = b.binary(Binary::Add, dead, dead);
        b.convert(Class::Fixed { bits: 4 }, also_dead);
        b.ret(&[kept]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, |_| true), 1, "the one constant it returns");
    assert_eq!(returns(&held), BigUint::from(7u8));
}

/// An arm that does something runs for what it does. Nobody wanting its
/// answer is not nobody wanting it.
#[test]
fn a_branch_nothing_reads_stays_for_what_its_arms_do() {
    let (mut p, main) = Program::new("main");
    let note = p.external("note", &[Class::Word], Returns::Values(&[]));
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let test = b.compare(Relation::Less, zero, one);
        b.if_(
            test,
            &[],
            |b| {
                let held = b.constant(Class::Word, 4);
                b.call(note, &[held]);
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.ret(&[zero]);
    });
    validate(&p).expect("a sound program");
    let held = optimize(&p, &OptimizeOptions::default());
    validate(&held).expect("a sound program");
    assert_eq!(count(&held, is_if), 1, "the branch stays");
    assert_eq!(count(&held, |op| matches!(*op, Op::Call { .. })), 1);
}

/// And one whose arms do nothing, and whose answer nothing reads, is gone
/// along with the comparison it asked.
#[test]
fn a_branch_that_does_nothing_and_answers_nobody_goes() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let test = b.compare(Relation::Less, zero, one);
        arms(b, test);
        b.ret(&[zero]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, is_if), 0);
    assert_eq!(count(&held, |op| matches!(*op, Op::Compare { .. })), 0);
    assert_eq!(count(&held, |_| true), 1, "the constant it returns");
}

/// Turning a stage off leaves its shapes where they were, which is what
/// says the schedule is two stages rather than one.
#[test]
fn each_stage_can_be_left_out() {
    let p = tagged((1, 0));
    let fused = optimize(
        &p,
        &OptimizeOptions {
            simplify: true,
            prune: false,
        },
    );
    assert_eq!(count(&fused, is_if), 2, "the tag is written and unread");
    let swept = optimize(
        &p,
        &OptimizeOptions {
            simplify: false,
            prune: true,
        },
    );
    assert_eq!(count(&swept, is_if), 2, "nothing recognised it");
    for held in [&fused, &swept] {
        validate(held).expect("a sound program");
        assert_eq!(returns(held), BigUint::from(20u8));
    }
}
