use super::*;

fn rejects(program: &Program, message: &str) {
    let error = validate(program).expect_err("malformed IR must be rejected");
    assert!(
        error.contains(message),
        "expected {message:?}, got {error:?}"
    );
}

fn simple() -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 1);
        b.ret(&[value]);
    });
    p
}

#[test]
fn branch_locals_cannot_escape_to_parent_or_sibling() {
    for sibling in [false, true] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let condition = b.constant(Class::Word, 1);
            let escaped = std::cell::Cell::new(condition);
            b.if_(
                condition,
                &[],
                |b| {
                    escaped.set(b.constant(Class::Word, 2));
                    b.yield_(&[]);
                },
                |b| {
                    if sibling {
                        b.binary(Binary::Add, escaped.get(), condition);
                    }
                    b.yield_(&[]);
                },
            );
            b.ret(&[escaped.get()]);
        });
        rejects(&p, "before it is available");
    }
}

#[test]
fn loop_parameters_and_locals_do_not_escape() {
    for parameter in [false, true] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let initial = b.constant(Class::Word, 0);
            let mut escaped = initial;
            b.loop_(&[initial], &[], |b, params| {
                escaped = if parameter {
                    params[0]
                } else {
                    b.constant(Class::Word, 1)
                };
                b.break_(&[]);
            });
            b.ret(&[escaped]);
        });
        rejects(&p, "before it is available");
    }
}

#[test]
fn only_the_target_may_enter_the_logical_entry() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let values = b.call(main, &[]);
        b.ret(&values);
    });
    rejects(&p, "only the target may enter");
}

#[test]
fn values_from_another_function_are_not_in_scope() {
    let (mut p, main) = Program::new("main");
    let other = p.declare("other", &[Class::Word], &[]);
    let mut escaped = ValueId(0);
    p.define(other, |b, params| {
        escaped = params[0];
        b.ret(&[]);
    });
    p.define(main, |b, _| b.ret(&[escaped]));
    rejects(&p, "before it is available");
}

#[test]
fn use_before_definition_and_self_reference_are_rejected() {
    for operand in [ValueId(0), ValueId(1)] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let first = b.constant(Class::Word, 1);
            let second = b.constant(Class::Word, 2);
            b.ret(&[second, first]);
        });
        p.ops[0] = Op::Binary {
            op: Binary::Add,
            left: operand,
            right: operand,
        };
        rejects(&p, "before it is available");
    }
}

#[test]
fn every_definition_is_unique_including_parameters() {
    let mut p = simple();
    p.ops.push(p.ops[0]);
    p.results.push(p.results[0]);
    p.regions[RegionId(0)].ops = Range::of(0, 2);
    rejects(&p, "defines ValueId(0) twice");

    let (mut p, main) = Program::new("main");
    let other = p.declare("other", &[Class::Word, Class::Word], &[]);
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 0);
        b.ret(&[value]);
    });
    p.define(other, |b, _| b.ret(&[]));
    let params = p.region(p.functions[FunctionId(1)].body().unwrap()).params;
    p.operands[params.range().start + 1] = p.operands[params.range().start];
    rejects(&p, "twice");
}

#[test]
fn function_and_branch_parameters_must_match_their_owner() {
    let mut p = simple();
    p.regions[RegionId(0)].params = p.results[0];
    rejects(&p, "function and body parameters disagree");

    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 1);
        b.if_(value, &[], |b| b.yield_(&[]), |b| b.yield_(&[]));
        b.ret(&[value]);
    });
    p.regions[RegionId(1)].params = p.results[0];
    rejects(&p, "branch region cannot have parameters");
}

#[test]
fn all_leaf_operations_check_result_arity_and_class() {
    let (mut p, main) = Program::new("main");
    let datum = p.intern(&[0; 8]);
    let argc = crate::platform::Routines::builtin().declare(&mut p, "argc!");
    let other = p.declare("other", &[], &[Class::Word]);
    p.define(other, |b, _| {
        let value = b.constant(Class::Word, 1);
        b.ret(&[value]);
    });
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 1);
        b.natural(&num_bigint::BigUint::from(1u8));
        let address = b.address_of(datum);
        b.binary(Binary::Add, value, value);
        b.compare(Relation::Equal, value, value);
        b.load(Width::Byte, address, Offset::Bytes(0));
        b.store(Width::Byte, address, Offset::Bytes(0), value);
        b.convert(Class::fixed(8), value);
        b.call(other, &[]);
        b.call(argc, &[]);
        b.ret(&[value]);
    });
    validate(&p).unwrap();
    for at in p.region(p.functions[p.entry()].body().unwrap()).ops.range() {
        let mut wrong_arity = p.clone();
        if p.results[at].is_empty() {
            wrong_arity.results[at] = p.results[0];
        } else {
            wrong_arity.results[at] = Range::EMPTY;
        }
        assert!(validate(&wrong_arity).is_err(), "{:?}", p.ops[at]);

        wrong_class(&p, at);
    }
}

/// Hold what an instruction writes at another class, where the instruction
/// says what it writes.
///
/// A constant and a conversion are held at whatever the value they write is
/// held at, and an address is one of the things either may answer, so there
/// is nothing about those two for a class to be wrong about.
fn wrong_class(p: &Program, at: usize) {
    if matches!(p.ops[at], Op::Constant { .. } | Op::Convert { .. }) {
        return;
    }
    let Some(&value) = p.values(p.results[at]).first() else {
        return;
    };
    let mut held = p.clone();
    held.classes[value] = if p.class(value) == Class::Address {
        Class::Word
    } else {
        Class::Address
    };
    assert!(validate(&held).is_err(), "{:?}", p.ops[at]);
}

#[test]
fn conditions_arithmetic_comparison_and_memory_need_suitable_classes() {
    for case in 0..8 {
        let (mut p, main) = Program::new("main");
        let datum = p.intern(&[0; 8]);
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 1);
            let address = b.address_of(datum);
            let natural = b.constant(Class::Natural, 2);
            match case {
                0 => {
                    b.if_(address, &[], |b| b.yield_(&[]), |b| b.yield_(&[]));
                }
                1 => {
                    b.binary(Binary::Add, address, address);
                }
                2 => {
                    b.compare(Relation::Equal, word, address);
                }
                3 => {
                    b.load(Width::Word, word, Offset::Words(0));
                }
                4 => b.store(Width::Word, word, Offset::Words(0), word),
                5 => b.store(Width::Byte, address, Offset::Bytes(0), address),
                6 => b.store(Width::Word, address, Offset::Words(0), natural),
                _ => {
                    b.convert(Class::Natural, address);
                }
            }
            b.ret(&[word]);
        });
        assert!(validate(&p).is_err(), "case {case}");
    }
}

#[test]
fn terminators_need_a_receiver_and_the_right_values() {
    for exit in [Exit::Yield, Exit::Break, Exit::Continue, Exit::Return] {
        let mut p = simple();
        p.regions[RegionId(0)].terminator.as_mut().unwrap().exit = exit;
        if exit == Exit::Return {
            p.regions[RegionId(0)].terminator.as_mut().unwrap().values = Range::EMPTY;
        }
        assert!(validate(&p).is_err(), "{exit:?}");
    }
}

#[test]
fn branch_yields_check_both_arity_and_class() {
    for wrong_class in [false, true] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 1);
            let answer = b.if_(
                word,
                &[Class::Word],
                |b| {
                    if wrong_class {
                        let address = b.constant(Class::Address, 0);
                        b.yield_(&[address]);
                    } else {
                        b.yield_(&[]);
                    }
                },
                |b| b.yield_(&[word]),
            );
            b.ret(&answer);
        });
        rejects(&p, "Yield");
    }
}

#[test]
fn loop_initial_continue_and_break_values_are_checked() {
    for exit in [Exit::Continue, Exit::Break, Exit::Yield] {
        for wrong_class in [false, true] {
            let (mut p, main) = Program::new("main");
            p.define(main, |b, _| {
                let word = b.constant(Class::Word, 1);
                b.loop_(&[word], &[Class::Word], |b, _| {
                    let address = b.constant(Class::Address, 0);
                    let values = if wrong_class { &[address][..] } else { &[] };
                    match exit {
                        Exit::Continue => b.continue_(values),
                        Exit::Break => b.break_(values),
                        _ => b.yield_(values),
                    }
                });
                b.ret(&[word]);
            });
            rejects(&p, &format!("{exit:?}"));
        }
    }
    for wrong_class in [false, true] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 1);
            b.loop_(&[word], &[], |b, _| b.break_(&[]));
            b.ret(&[word]);
        });
        if wrong_class {
            let body = p.regions[RegionId(1)];
            let param = p.values(body.params)[0];
            p.classes[param] = Class::Address;
        } else if let Op::Loop { initial, .. } = &mut p.ops[1] {
            *initial = Range::EMPTY;
        }
        rejects(&p, "loop initial values");
    }
}

#[test]
fn nested_controls_use_the_nearest_loop_and_allow_early_return() {
    let (mut p, main) = Program::new("main");
    let exit = crate::platform::Routines::builtin().declare(&mut p, "exit!");
    p.define(main, |b, _| {
        let word = b.constant(Class::Word, 1);
        let result = b.loop_(&[word], &[Class::Word], |b, params| {
            let carried = params[0];
            b.loop_(&[], &[], |b, _| b.break_(&[]));
            b.if_(
                word,
                &[],
                |b| {
                    b.if_(
                        word,
                        &[],
                        |b| b.continue_(&[carried]),
                        |b| b.break_(&[carried]),
                    );
                },
                |b| {
                    b.if_(
                        word,
                        &[Class::Word],
                        |b| b.ret(&[carried]),
                        |b| {
                            b.call(exit, &[word]);
                        },
                    );
                },
            );
        });
        b.ret(&result);
    });
    validate(&p).unwrap();
}

#[test]
fn conversions_pointer_memory_and_narrow_control_values_remain_valid() {
    let (mut p, main) = Program::new("main");
    let data = p.global(&[0; 8]);
    p.define(main, |b, _| {
        let byte = b.constant(Class::fixed(8), 1);
        let address = b.address_of(data);
        b.store(Width::Word, address, Offset::Words(0), address);
        let word = b.convert(Class::Word, address);
        b.convert(Class::Address, word);
        let natural = b.convert(Class::Natural, byte);
        b.convert(Class::fixed(8), natural);
        let answer = b.if_(
            byte,
            &[Class::Word],
            |b| b.yield_(&[byte]),
            |b| b.ret(&[byte]),
        );
        b.ret(&answer);
    });
    validate(&p).unwrap();
}

#[test]
fn invalid_public_ids_and_ranges_return_errors_instead_of_panicking() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        b.address_of(DataId(u32::MAX));
        b.ret(&[]);
    });
    rejects(&p, "invalid datum reference");

    let mut p = simple();
    p.regions[RegionId(0)].terminator.as_mut().unwrap().values =
        Range::of(usize::try_from(u32::MAX).unwrap(), 2);
    rejects(&p, "invalid pool range");
    let mut p = simple();
    p.regions[RegionId(0)].terminator.as_mut().unwrap().values = p.hold(&[ValueId(u32::MAX)]);
    rejects(&p, "invalid value reference");

    for op in [
        Op::Call {
            function: FunctionId(u32::MAX),
            args: Range::EMPTY,
        },
        Op::Loop {
            initial: Range::EMPTY,
            body: RegionId(u32::MAX),
        },
        Op::NaturalConstant(DataId(u32::MAX)),
    ] {
        let mut p = simple();
        p.ops[0] = op;
        rejects(&p, "invalid");
    }
}

#[test]
fn corrupt_declaration_and_storage_pools_are_rejected() {
    let mut p = simple();
    p.functions[FunctionId(0)].name = model::Symbol(u32::MAX);
    rejects(&p, "invalid symbol");
    let mut p = simple();
    p.names[0] = 255;
    rejects(&p, "invalid name text");
    let mut p = simple();
    p.functions[FunctionId(0)].returns = Returns::Values(Range::of(100, 1));
    rejects(&p, "invalid pool range");
    let mut p = simple();
    p.results.clear();
    rejects(&p, "different lengths");
    let mut p = simple();
    p.regions[RegionId(0)].ops = Range::of(100, 1);
    rejects(&p, "invalid pool range");
    let mut p = simple();
    p.spans.push(Span {
        origin: Origin::Data,
        start: 100,
        len: 1,
    });
    rejects(&p, "invalid pool range");
    let mut p = simple();
    let argc = crate::platform::Routines::builtin().declare(&mut p, "argc!");
    p.functions[argc].name = model::Symbol(u32::MAX);
    rejects(&p, "invalid symbol");
}

#[test]
fn cyclic_and_shared_regions_are_rejected() {
    let mut p = simple();
    p.ops[0] = Op::Loop {
        initial: Range::EMPTY,
        body: RegionId(0),
    };
    rejects(&p, "cyclic or has multiple owners");

    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let word = b.constant(Class::Word, 0);
        b.if_(word, &[], |b| b.yield_(&[]), |b| b.yield_(&[]));
        b.ret(&[word]);
    });
    if let Op::If {
        then_region,
        else_region,
        ..
    } = &mut p.ops[1]
    {
        *else_region = *then_region;
    }
    rejects(&p, "cyclic or has multiple owners");
}

#[test]
fn existing_target_fixture_programs_validate() {
    for (name, p, _) in crate::programs::printing() {
        validate(&p).unwrap_or_else(|error| panic!("{name}: {error}"));
    }
}
