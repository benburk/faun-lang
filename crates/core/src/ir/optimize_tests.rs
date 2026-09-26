//! What the machine passes recognise, what they leave alone, and that a
//! program answers the same either way.
//!
//! Programs here are written straight into machine IR rather than read from
//! source, so each one says only the shape it is about. What lowering
//! actually writes is the frontend's business, and shown where it is read.

use num_bigint::BigUint;

use crate::facts::Facts;

use super::{Binary, Class, Op, Program, Relation, Returns, ValueId, evaluate, optimize, validate};

const BIT: Class = Class::fixed(1);

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
    let held = optimize(p);
    assert_eq!(returns(&held), before, "a pass changed what it answers");
    held
}

fn count(p: &Program, wanted: impl Fn(&Op) -> bool) -> usize {
    let body = p.function(p.entry()).body().expect("a body");
    p.every(body).filter(|op| wanted(op)).count()
}

/// The same, where what an instruction writes is held at decides.
fn count_at(p: &Program, wanted: impl Fn(&Op, Class) -> bool) -> usize {
    let body = p.function(p.entry()).body().expect("a body");
    p.walk_within(body)
        .filter(|(op, results)| {
            results
                .first()
                .is_some_and(|&value| wanted(op, p.class(value)))
        })
        .count()
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
    let wide = Class::fixed(9);
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let narrow = b.constant(Class::fixed(3), 5);
        let read = b.convert(wide, narrow);
        let other = b.constant(wide, 256);
        let total = b.binary(Binary::Add, read, other);
        let answer = b.convert(Class::Word, total);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    // Nothing widens it: what three bits can be, nine bits admit, so the
    // constant is read where it stands and stays as narrow as it is.
    assert_eq!(
        count_at(&held, |op, class| {
            matches!(*op, Op::Convert { .. }) && class == wide
        }),
        0,
        "nothing is widened to be read"
    );
    assert_eq!(
        count_at(&held, |op, class| {
            *op == Op::Constant { value: 5 } && class == Class::fixed(3)
        }),
        1
    );
    assert_eq!(returns(&held), BigUint::from(261u16));
}

/// Read narrower, a constant is the number that fits, which is what writing
/// it at that width already means.
#[test]
fn a_constant_read_narrower_is_the_number_that_fits() {
    let narrow = Class::fixed(3);
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let wide = b.constant(Class::fixed(9), 13);
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
        b.convert(Class::fixed(4), also_dead);
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
    let held = optimize(&p);
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

/// Each stage alone leaves the other's shapes where they were, which is
/// what says the schedule is two stages rather than one.
#[test]
fn each_stage_alone_does_only_its_own_part() {
    let p = tagged((1, 0));
    let fused = super::simplify::simplify(&p);
    assert_eq!(count(&fused, is_if), 2, "the tag is written and unread");
    let swept = super::prune::prune(&p);
    assert_eq!(count(&swept, is_if), 2, "nothing recognised it");
    for held in [&fused, &swept] {
        validate(held).expect("a sound program");
        assert_eq!(returns(held), BigUint::from(20u8));
    }
}

/// A number reached by adding one four times is that number plus four.
///
/// One past another is a constructor where a program is written, and the
/// tier above has no addition to fold a run of them into. This one does.
#[test]
fn a_run_of_steps_past_a_value_is_one_step() {
    let held = settled(&stepped(WIDE, &[1, 1, 1, 1]));
    assert_eq!(count(&held, is_add), 1, "one step, not four");
    // The number it steps by can be nothing but four.
    assert_eq!(
        count_at(&held, |op, class| {
            *op == Op::Constant { value: 4 } && class == Class::Held(Facts::at(4))
        }),
        1
    );
    assert_eq!(
        returns(&held),
        BigUint::from(7u8),
        "three, and four past it"
    );
}

/// A run whose total does not fit the width it is taken at is not a run
/// this can say anything about.
///
/// No valid program has one: where each step fits, so does their total. So
/// what this is about is an invalid program not being quietly turned into a
/// valid-looking one that answers something else.
#[test]
fn a_run_that_would_not_fit_its_width_is_left_alone() {
    let narrow = Class::fixed(3);
    // Three, and eight past it, which three bits do not hold.
    let held = optimize(&stepped(narrow, &[4, 4]));
    validate(&held).expect("a sound program");
    assert_eq!(count(&held, is_add), 2, "eight would not fit three bits");
}

/// One taken at a wider width than the step before it asserts something the
/// narrower one did not, so the two are not one step.
#[test]
fn a_run_that_changes_width_is_two_runs() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let narrow = Class::fixed(3);
        let start = unknown(b, narrow, 1);
        let one = b.constant(narrow, 1);
        let held = b.binary_at(narrow, Binary::Add, start, one);
        let wide = b.convert(WIDE, held);
        let two = b.constant(WIDE, 2);
        let total = b.binary_at(WIDE, Binary::Add, wide, two);
        let answer = b.convert(Class::Word, total);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, is_add), 2);
    assert_eq!(returns(&held), BigUint::from(4u8));
}

/// A value part way along a run is still worked out for whoever reads it.
#[test]
fn a_step_something_reads_survives_the_run_it_is_part_of() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let start = unknown(b, WIDE, 0);
        let one = b.constant(WIDE, 1);
        let first = b.binary_at(WIDE, Binary::Add, start, one);
        let second = b.binary_at(WIDE, Binary::Add, first, one);
        // Both ends of the run are read, so both are written.
        let total = b.binary_at(WIDE, Binary::Add, first, second);
        let answer = b.convert(Class::Word, total);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, is_add), 3, "the run, and what reads into it");
    assert_eq!(returns(&held), BigUint::from(3u8), "one and two");
}

/// A step of something worked out is not a step of a known number. It is a
/// doubling, which is a shift, and the run it steps from stays a run.
#[test]
fn a_step_of_something_worked_out_is_left_alone() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let start = unknown(b, WIDE, 1);
        let one = b.constant(WIDE, 1);
        let held = b.binary_at(WIDE, Binary::Add, start, one);
        let doubled = b.binary_at(WIDE, Binary::Add, held, held);
        let answer = b.convert(Class::Word, doubled);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, is_add), 1, "the run it steps from");
    assert_eq!(count(&held, is_shift), 1, "the doubling");
    assert_eq!(returns(&held), BigUint::from(4u8));
}

/// A product or quotient by a power of two is the shift it is, and by
/// anything else is left where it stands.
#[test]
fn a_product_by_a_power_of_two_is_a_shift() {
    for (by, shifts, adds) in [(2u64, 1, 0), (8, 1, 0), (3, 0, 0), (1, 0, 0)] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let start = unknown(b, WIDE, 1);
            let places = b.constant(WIDE, by);
            let held = b.binary_at(WIDE, Binary::Mul, start, places);
            let answer = b.convert(Class::Word, held);
            b.ret(&[answer]);
        });
        let held = settled(&p);
        assert_eq!(count(&held, is_shift), shifts, "a product by {by}");
        assert_eq!(count(&held, is_add), adds, "a product by {by}");
        assert_eq!(returns(&held), BigUint::from(by), "one times {by}");
    }
}

/// A quotient too, and the distance has to be one every target can take.
#[test]
fn a_quotient_by_a_power_of_two_is_a_shift() {
    // Nine bits wide, so eight places is a shift and nine is not: a machine
    // told to move a value further than it is wide answers something else.
    for (by, shifts) in [(2u64, 1), (256, 1), (512, 0), (6, 0)] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let start = unknown(b, WIDE, 384);
            let places = b.constant(WIDE, by);
            let held = b.binary_at(WIDE, Binary::Div, start, places);
            let answer = b.convert(Class::Word, held);
            b.ret(&[answer]);
        });
        let held = settled(&p);
        assert_eq!(count(&held, is_shift), shifts, "a quotient by {by}");
        assert_eq!(returns(&held), BigUint::from(384 / by), "384 over {by}");
    }
}

const WIDE: Class = Class::fixed(9);

/// `value` at `class`, where no pass can see it: whichever arm a comparison
/// chose, each answering it. Arithmetic on it is arithmetic on something
/// worked out, which is what a pass recognising shapes of arithmetic reads.
fn unknown(b: &mut super::Builder, class: Class, value: u64) -> ValueId {
    let zero = b.constant(Class::Word, 0);
    let one = b.constant(Class::Word, 1);
    let test = b.compare(Relation::Less, zero, one);
    b.if_(
        test,
        &[class],
        |b| {
            let held = b.constant(class, value);
            b.yield_(&[held]);
        },
        |b| {
            let held = b.constant(class, value);
            b.yield_(&[held]);
        },
    )[0]
}

/// Arithmetic on numbers known before the program runs is the number it
/// comes to, and an identity is what it was applied to.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one table of folds and one of identities, each checked against the reference"
)]
fn arithmetic_on_known_numbers_is_the_number_it_comes_to() {
    for (op, x, y) in [
        (Binary::Add, 300, 11),
        (Binary::Sub, 300, 11),
        (Binary::Monus, 11, 300),
        (Binary::Mul, 20, 25),
        (Binary::Div, 300, 0),
        (Binary::Mod, 300, 0),
        (Binary::Mod, 300, 7),
    ] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let left = b.constant(WIDE, x);
            let right = b.constant(WIDE, y);
            let held = b.binary_at(WIDE, op, left, right);
            let answer = b.convert(Class::Word, held);
            b.ret(&[answer]);
        });
        let held = settled(&p);
        assert_eq!(
            count(&held, |op| matches!(
                *op,
                Op::Binary { .. } | Op::Shift { .. }
            )),
            0,
            "{op:?} of {x} and {y}"
        );
    }
    for (op, known, left_known) in [
        (Binary::Add, 0, true),
        (Binary::Add, 0, false),
        (Binary::Sub, 0, false),
        (Binary::Mul, 1, true),
        (Binary::Div, 1, false),
    ] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let held = unknown(b, WIDE, 300);
            let known = b.constant(WIDE, known);
            let (left, right) = if left_known {
                (known, held)
            } else {
                (held, known)
            };
            let answer = b.binary_at(WIDE, op, left, right);
            let answer = b.convert(Class::Word, answer);
            b.ret(&[answer]);
        });
        let held = settled(&p);
        assert_eq!(
            count(&held, |op| matches!(*op, Op::Binary { .. })),
            0,
            "{op:?} by {known}"
        );
        assert_eq!(returns(&held), BigUint::from(300u16));
    }
}

/// A sum that would not fit the class it is claimed to fit is not folded
/// into a number that does: that would be a pass choosing a modulus.
#[test]
fn a_known_sum_too_wide_for_its_class_is_left_alone() {
    let narrow = Class::fixed(3);
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let left = b.constant(narrow, 6);
        let right = b.constant(narrow, 5);
        let held = b.binary_at(narrow, Binary::Add, left, right);
        let answer = b.convert(Class::Word, held);
        b.ret(&[answer]);
    });
    let held = optimize(&p);
    validate(&held).expect("a sound program");
    assert_eq!(count(&held, is_add), 1);
}

const fn is_add(op: &Op) -> bool {
    matches!(
        *op,
        Op::Binary {
            op: Binary::Add,
            ..
        }
    )
}

const fn is_shift(op: &Op) -> bool {
    matches!(*op, Op::Shift { .. })
}

/// Three, then each of `by` added to it in turn, answered as a word.
fn stepped(class: Class, by: &[u64]) -> Program {
    let (mut p, main) = Program::new("main");
    let by = by.to_vec();
    p.define(main, |b, _| {
        let mut held = unknown(b, class, 3);
        for step in by {
            let step = b.constant(class, step);
            held = b.binary_at(class, Binary::Add, held, step);
        }
        let answer = b.convert(Class::Word, held);
        b.ret(&[answer]);
    });
    p
}

/// A remainder by a power of two is every bit below it, which is what
/// reading a value at that width already means.
#[test]
fn a_remainder_by_a_power_of_two_is_a_width() {
    for (by, bits) in [(256u64, 8), (4, 2), (1, 0)] {
        let held = settled(&remainder(by, 300));
        assert_eq!(
            count(&held, |op| matches!(
                *op,
                Op::Binary {
                    op: Binary::Mod,
                    ..
                }
            )),
            0,
            "by {by}"
        );
        assert_eq!(returns(&held), BigUint::from(300 % by), "by {by}");
        assert!(
            count_at(&held, |_, class| class == Class::fixed(bits)) > 0,
            "by {by}: read at {bits} bits"
        );
    }
}

/// By anything else it is a division, and stays one.
#[test]
fn a_remainder_by_anything_else_is_left_as_it_stands() {
    let held = settled(&remainder(10, 300));
    assert_eq!(
        count(&held, |op| matches!(
            *op,
            Op::Binary {
                op: Binary::Mod,
                ..
            }
        )),
        1
    );
    assert_eq!(returns(&held), BigUint::from(0u8), "300 mod 10");
}

/// A difference that stops at nought, asked whether it is nought, is asking
/// whether one number is no more than the other: one comparison, and no
/// subtraction left, answering what the two did.
#[test]
fn a_difference_asked_whether_it_is_nought_is_a_comparison() {
    for value in [100u64, 200, 201, 300] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let class = Class::fixed(9);
            let held = unknown(b, class, value);
            let bound = b.constant(class, 200);
            let rest = b.binary_at(class, Binary::Monus, held, bound);
            let nought = b.constant(class, 0);
            let at_most = b.compare(Relation::Equal, rest, nought);
            b.ret(&[at_most]);
        });
        let held = settled(&p);
        let monus = |op: &Op| {
            matches!(
                *op,
                Op::Binary {
                    op: Binary::Monus,
                    ..
                }
            )
        };
        assert_eq!(count(&held, monus), 0, "{value}");
        assert_eq!(
            returns(&held),
            BigUint::from(u8::from(value <= 200)),
            "{value}"
        );
    }
}

/// A value already narrow enough is read where it stands.
#[test]
fn a_conversion_that_takes_nothing_off_is_not_written() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let held = b.constant(Class::fixed(3), 5);
        let wider = b.convert(Class::fixed(9), held);
        let answer = b.convert(Class::Word, wider);
        b.ret(&[answer]);
    });
    let held = settled(&p);
    assert_eq!(count(&held, |op| matches!(*op, Op::Convert { .. })), 0);
    assert_eq!(returns(&held), BigUint::from(5u8));
}

/// `value % by`, answered as a word.
fn remainder(by: u64, value: u64) -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let class = Class::fixed(9);
        let held = unknown(b, class, value);
        let by = b.constant(class, by);
        let answer = b.binary_at(class, Binary::Mod, held, by);
        let answer = b.convert(Class::Word, answer);
        b.ret(&[answer]);
    });
    p
}
