use super::evaluate::{self, Config, Error, Host, HostResult, Memory, RejectHost};
use super::*;
use num_bigint::BigUint;

fn rejects(p: &Program, message: &str) {
    let error = validate(p).unwrap_err();
    assert!(error.contains(message), "{error}");
}

#[test]
fn declarations_and_built_but_incomplete_bodies_are_different_errors() {
    let (mut p, main) = Program::new("main");
    assert!(p.function(p.entry()).body().is_none());
    assert_eq!(
        evaluate::evaluate(&p, main, &[], Config::default(), &mut RejectHost),
        Err(Error::InvalidProgram("function has not been defined"))
    );
    rejects(&p, "has not been defined");
    p.define(main, |_, _| {});
    assert!(p.function(p.entry()).body().is_some());
    rejects(&p, "can fall through but has no terminator");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    p.declare("unused", &[], &[]);
    rejects(&p, "`unused` has not been defined");
}

#[test]
fn returning_no_values_is_not_terminal() {
    let (mut p, main) = Program::new("main");
    let call = p.external("unit", &[], Returns::Values(&[]));
    p.define(main, |b, _| {
        b.call(call, &[]);
    });
    rejects(&p, "can fall through");
}

#[test]
fn never_calls_need_no_marker_and_reject_following_code_or_transfers() {
    for following in 0..3 {
        let (mut p, main) = Program::new("main");
        let stop = p.external("stop", &[], Returns::Never);
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 0);
            b.call(stop, &[]);
            match following {
                0 => {}
                1 => b.ret(&[word]),
                _ => {
                    b.constant(Class::Word, 1);
                }
            }
        });
        if following == 0 {
            validate(&p).unwrap();
            assert!(
                p.region(p.function(p.entry()).body().unwrap())
                    .terminator
                    .is_none()
            );
        } else {
            rejects(&p, "does not come back");
        }
    }
}

#[test]
fn terminal_branches_reject_both_extra_instructions_and_extra_transfers() {
    for following in 0..3 {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 7);
            b.if_(word, &[], |b| b.ret(&[word]), |b| b.ret(&[word]));
            match following {
                0 => {}
                1 => b.ret(&[word]),
                _ => {
                    b.constant(Class::Word, 1);
                }
            }
        });
        if following == 0 {
            validate(&p).unwrap();
        } else {
            rejects(&p, "does not come back");
        }
    }
}

#[test]
fn yielding_branches_and_breaking_loops_still_need_a_continuation() {
    for case in 0..4 {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 7);
            match case {
                0 => {
                    b.if_(word, &[], |b| b.ret(&[word]), |b| b.yield_(&[]));
                }
                1 => {
                    b.if_(word, &[], |b| b.yield_(&[]), |b| b.yield_(&[]));
                }
                2 => {
                    b.loop_(&[], &[], |b, _| b.break_(&[]));
                }
                _ => {
                    b.if_(word, &[], |_| {}, |b| b.ret(&[word]));
                }
            }
        });
        rejects(&p, "can fall through");
    }
}

#[test]
fn nested_yields_and_breaks_do_not_finish_the_enclosing_region() {
    for inside_loop in [false, true] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 1);
            if inside_loop {
                b.loop_(&[], &[], |b, _| {
                    b.if_(word, &[], |b| b.yield_(&[]), |b| b.yield_(&[]));
                });
            } else {
                b.if_(
                    word,
                    &[],
                    |b| {
                        b.loop_(&[], &[], |b, _| b.break_(&[]));
                    },
                    |b| b.ret(&[word]),
                );
            }
        });
        rejects(&p, "can fall through");
    }
}

#[test]
fn a_nested_loops_break_does_not_make_an_outer_loop_return() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        b.loop_(&[], &[], |b, _| {
            b.loop_(&[], &[], |b, _| b.break_(&[]));
            b.continue_(&[]);
        });
    });
    validate(&p).unwrap();
    assert_eq!(
        evaluate::evaluate(
            &p,
            main,
            &[],
            Config {
                fuel: 50,
                ..Config::default()
            },
            &mut RejectHost
        ),
        Err(Error::FuelExhausted)
    );
    p.regions[RegionId(0)].terminator = Some(Terminator {
        exit: Exit::Return,
        values: Range::EMPTY,
    });
    rejects(&p, "does not come back");
}

struct Stop;
impl Host for Stop {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        assert_eq!(name, "stop");
        Ok(HostResult::Halt(args.to_vec()))
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "build, legalize and run both paths at every word width"
)]
fn an_earlier_branch_break_survives_a_terminal_tail_and_legalization() {
    for condition in [0, 1] {
        let (mut p, main) = Program::new("main");
        let stop = p.external("stop", &[Class::Word], Returns::Never);
        p.define(main, |b, _| {
            let condition = b.constant(Class::Word, condition);
            let value = b.natural(&(BigUint::from(1u8) << 128usize));
            let result = b.loop_(&[], &[Class::Natural], |b, _| {
                b.if_(condition, &[], |b| b.break_(&[value]), |b| b.yield_(&[]));
                b.call(stop, &[condition]);
            });
            let equal = b.compare(Relation::Equal, result[0], value);
            b.ret(&[equal]);
        });
        validate(&p).unwrap();
        for word_bits in [16, 32, 64] {
            let rebuilt = legalize(
                &p,
                natural::Config {
                    word_bits,
                    heap_bytes: 512,
                },
            )
            .unwrap();
            validate(&rebuilt).unwrap();
            for program in [&p, &rebuilt] {
                let answer = evaluate::evaluate(
                    program,
                    main,
                    &[],
                    Config {
                        word_bits,
                        ..Config::default()
                    },
                    &mut Stop,
                )
                .unwrap();
                if condition == 0 {
                    assert_eq!(answer.halted().unwrap(), &[BigUint::from(0u8)]);
                } else {
                    assert_eq!(answer.returned().unwrap(), &[BigUint::from(1u8)]);
                }
            }
        }
    }
}

#[test]
fn internal_never_contracts_propagate_but_cannot_return_unit() {
    let (mut p, main) = Program::new("main");
    let forever = p.declare_never("forever", &[]);
    p.define(main, |b, _| {
        b.call(forever, &[]);
    });
    p.define(forever, |b, _| {
        b.loop_(&[], &[], |b, _| b.continue_(&[]));
    });
    validate(&p).unwrap();
    p.define(forever, |b, _| b.ret(&[]));
    rejects(&p, "Return has no enclosing receiver");
}

#[test]
fn source_never_functions_keep_their_contract_without_inlining() {
    let routines = crate::platform::Routines::builtin().with_word(64);
    let mut source = crate::simple::parse(
        "type Nat Zero Succ(Nat)\nfinish!(h) -> exit!(h Zero)\nmain!(h) -> finish!(h)",
        &routines,
    )
    .unwrap();
    let p = lower(source.analyze(), &routines).unwrap();
    validate(&p).unwrap();
    assert_eq!(
        p.functions().iter().filter(|f| f.body().is_some()).count(),
        2
    );
    assert_eq!(
        p.functions()
            .iter()
            .filter(|f| f.body().is_some() && f.returns == Returns::Never)
            .count(),
        1
    );
}

#[test]
#[should_panic(expected = "a terminated region cannot be extended")]
fn an_explicit_transfer_cannot_be_overwritten() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let word = b.constant(Class::Word, 0);
        b.ret(&[word]);
        b.ret(&[word]);
    });
}

#[test]
#[should_panic(expected = "a terminated region cannot be extended")]
fn an_instruction_cannot_be_reordered_before_an_explicit_transfer() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let word = b.constant(Class::Word, 0);
        b.ret(&[word]);
        b.constant(Class::Word, 1);
    });
}
