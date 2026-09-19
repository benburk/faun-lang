use super::evaluate::{
    Config, Endian, Error, Evaluation, Host, HostResult, Memory, RejectHost, evaluate,
};
use super::*;
use num_bigint::BigUint;

fn run(
    program: &Program,
    function: FunctionId,
    args: &[u64],
    bits: u16,
) -> Result<Evaluation, Error> {
    evaluate(
        program,
        function,
        &args.iter().copied().map(BigUint::from).collect::<Vec<_>>(),
        Config {
            word_bits: bits,
            ..Config::default()
        },
        &mut RejectHost,
    )
}

fn division_program() -> (Program, FunctionId) {
    let (mut p, _) = Program::new("main");
    let divmod = p.declare(
        "divmod",
        &[Class::Word, Class::Word],
        &[Class::Word, Class::Word],
    );
    p.define(divmod, |b, args| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let is_zero = b.compare(Relation::Equal, args[1], zero);
        b.if_(is_zero, &[], |b| b.ret(&[zero, args[0]]), |b| b.yield_(&[]));
        let answer = b.loop_(&[zero, args[0]], &[Class::Word, Class::Word], |b, state| {
            let done = b.compare(Relation::Less, state[1], args[1]);
            b.if_(
                done,
                &[],
                |b| b.break_(state),
                |b| {
                    let q = b.binary(Binary::Add, state[0], one);
                    let r = b.binary(Binary::Sub, state[1], args[1]);
                    b.continue_(&[q, r])
                },
            );
            Terminator::UNREACHABLE
        });
        b.ret(&answer)
    });
    (p, divmod)
}

#[test]
fn loops_and_nested_exits_match_total_division_model_at_every_width() {
    let (p, divmod) = division_program();
    for bits in [16, 32, 64] {
        for left in 0u64..20 {
            for right in 0..8 {
                let expected = vec![
                    left.checked_div(right).unwrap_or(0),
                    left.checked_rem(right).unwrap_or(left),
                ];
                assert_eq!(
                    run(&p, divmod, &[left, right], bits)
                        .unwrap()
                        .returned()
                        .unwrap(),
                    expected.into_iter().map(BigUint::from).collect::<Vec<_>>()
                );
            }
        }
    }
}

#[test]
fn recursive_calls_keep_caller_frames_and_early_returns() {
    let (mut p, _) = Program::new("main");
    let sum = p.declare("sum", &[Class::Word], &[Class::Word]);
    p.define(sum, |b, args| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let done = b.compare(Relation::Equal, args[0], zero);
        b.if_(done, &[], |b| b.ret(&[zero]), |b| b.yield_(&[]));
        let n = b.binary(Binary::Sub, args[0], one);
        let tail = b.call(sum, &[n])[0];
        let result = b.binary(Binary::Add, args[0], tail);
        b.ret(&[result])
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, sum, &[100], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(5050u32)]
        );
    }
    // More recursive calls than would be safe on a native recursive evaluator.
    let f = p.declare("forever", &[], &[]);
    p.define(f, |b, _| {
        b.call(f, &[]);
        b.ret(&[])
    });
    assert_eq!(
        evaluate(
            &p,
            f,
            &[],
            Config {
                fuel: 10_000,
                ..Config::default()
            },
            &mut RejectHost
        ),
        Err(Error::FuelExhausted)
    );
}

fn natural_program() -> (Program, FunctionId) {
    let (mut p, _) = Program::new("main");
    let f = p.declare(
        "big",
        &[Class::Natural, Class::Natural],
        &[Class::Natural, Class::Natural, Class::Word],
    );
    p.define(f, |b, args| {
        let sum = b.binary(Binary::Add, args[0], args[1]);
        let difference = b.binary(Binary::Sub, args[1], args[0]);
        let word = b.convert(Class::Word, sum);
        b.ret(&[sum, difference, word])
    });
    (p, f)
}

#[test]
fn natural_arithmetic_is_not_a_word_and_conversion_is_explicit() {
    let (p, f) = natural_program();
    let large = (BigUint::from(1u8) << 200usize) + BigUint::from(41u8);
    for word_bits in [16, 32, 64] {
        let result = evaluate(
            &p,
            f,
            &[large.clone(), BigUint::from(1u8)],
            Config {
                word_bits,
                ..Config::default()
            },
            &mut RejectHost,
        )
        .unwrap();
        assert_eq!(
            result.returned().unwrap(),
            vec![
                &large + BigUint::from(1u8),
                BigUint::default(),
                BigUint::from(42u8)
            ]
        );
    }
    assert_eq!(
        evaluate(
            &p,
            f,
            &[large, BigUint::from(1u8)],
            Config {
                max_natural_bits: 128,
                ..Config::default()
            },
            &mut RejectHost
        ),
        Err(Error::SizeLimit)
    );
}

#[test]
fn natural_constants_and_fixed_arithmetic_check_their_fit() {
    let (mut p, main) = Program::new("main");
    let large = (BigUint::from(1u8) << 150usize) + BigUint::from(511u16);
    p.define(main, |b, _| {
        let large = b.natural(&large);
        let byte = b.convert(Class::Fixed { bits: 8 }, large);
        let one = b.constant(Class::Fixed { bits: 8 }, 1);
        let sum = b.binary_at(Class::Fixed { bits: 9 }, Binary::Add, byte, one);
        let word = b.convert(Class::Word, sum);
        b.ret(&[word])
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(256u16)]
        );
    }
    p.define(main, |b, _| {
        let max = b.constant(Class::Fixed { bits: 8 }, 255);
        let one = b.constant(Class::Fixed { bits: 8 }, 1);
        let overflow = b.binary(Binary::Add, max, one);
        let word = b.convert(Class::Word, overflow);
        b.ret(&[word])
    });
    assert_eq!(
        run(&p, main, &[], 64),
        Err(Error::DoesNotFit(Class::Fixed { bits: 8 }))
    );
    p.define(main, |b, _| {
        let zero = b.constant(Class::Fixed { bits: 8 }, 0);
        let one = b.constant(Class::Fixed { bits: 8 }, 1);
        let underflow = b.binary(Binary::Sub, zero, one);
        b.ret(&[underflow])
    });
    assert_eq!(
        run(&p, main, &[], 64),
        Err(Error::DoesNotFit(Class::Fixed { bits: 8 }))
    );
}

#[test]
fn words_wrap_at_the_configured_width_not_the_host_width() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let max = b.binary(Binary::Sub, zero, one);
        b.ret(&[max])
    });
    for bits in [16, 32, 64] {
        let max = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![max]
        );
    }
    for bits in [16, 32, 64] {
        p.define(main, |b, _| {
            let max = b.constant(Class::Word, u64::MAX >> (64 - bits));
            let one = b.constant(Class::Word, 1);
            let zero = b.binary(Binary::Add, max, one);
            b.ret(&[zero])
        });
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
    }
}

fn memory_program(word_bits: u16) -> (Program, FunctionId) {
    let (mut p, main) = Program::new("main");
    let data = p.intern(&[0x12, 0x34]);
    let global = p.global(&[0; 32]);
    p.define(main, |b, _| {
        let address = b.address_of(global);
        let source = b.address_of(data);
        let value = b.load(Width::Byte, source, Offset::Bytes(1));
        b.store(Width::Word, address, Offset::Words(1), value);
        let one_word = b.constant(Class::Word, u64::from(word_bits / 8));
        let address_word = b.convert(Class::Word, address);
        let next = b.binary(Binary::Add, address_word, one_word);
        let next = b.convert(Class::Address, next);
        b.store(Width::Byte, next, Offset::Words(-1), value);
        let answer = b.load(Width::Word, address, Offset::Words(1));
        b.ret(&[answer])
    });
    (p, main)
}

#[test]
fn memory_respects_endian_word_stride_and_negative_offsets() {
    for word_bits in [16, 32, 64] {
        for endian in [Endian::Little, Endian::Big] {
            let (p, main) = memory_program(word_bits);
            let result = evaluate(
                &p,
                main,
                &[],
                Config {
                    word_bits,
                    endian,
                    ..Config::default()
                },
                &mut RejectHost,
            )
            .unwrap();
            assert_eq!(result.returned().unwrap(), vec![BigUint::from(0x34u8)]);
            let stride = usize::from(word_bits / 8);
            let mut expected = vec![0; 32];
            expected[0] = 0x34;
            expected[if endian == Endian::Little {
                stride
            } else {
                2 * stride - 1
            }] = 0x34;
            assert_eq!(result.globals, expected);
        }
    }
}

#[test]
fn invalid_memory_widths_and_unreachable_are_errors() {
    let (mut p, main) = Program::new("main");
    let data = p.intern(&[0; 8]);
    for offset in [Offset::Bytes(-2), Offset::Bytes(8), Offset::Words(i32::MAX)] {
        p.define(main, |b, _| {
            let address = b.address_of(data);
            let value = b.load(Width::Byte, address, offset);
            b.ret(&[value])
        });
        for bits in [16, 32, 64] {
            assert_eq!(run(&p, main, &[], bits), Err(Error::InvalidMemory));
        }
    }
    p.define(main, |b, _| {
        let address = b.address_of(data);
        let zero = b.constant(Class::Word, 0);
        b.store(Width::Byte, address, Offset::Bytes(0), zero);
        b.ret(&[zero])
    });
    assert_eq!(run(&p, main, &[], 64), Err(Error::ReadOnlyMemory));
    p.define(main, |b, _| {
        let n = b.constant(Class::Fixed { bits: 17 }, 1);
        b.ret(&[n])
    });
    assert_eq!(
        run(&p, main, &[], 16),
        Err(Error::DoesNotFit(Class::Fixed { bits: 17 }))
    );
    assert_eq!(run(&p, main, &[], 8), Err(Error::InvalidConfig));
    p.define(main, |_, _| Terminator::UNREACHABLE);
    assert_eq!(run(&p, main, &[], 64), Err(Error::Unreachable));
}

#[test]
fn fuel_counts_instructions_and_terminators_including_empty_loops() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let n = b.constant(Class::Word, 7);
        b.ret(&[n])
    });
    let config = Config {
        fuel: 2,
        ..Config::default()
    };
    assert_eq!(
        evaluate(&p, main, &[], config, &mut RejectHost)
            .unwrap()
            .fuel_remaining,
        0
    );
    assert_eq!(
        evaluate(&p, main, &[], Config { fuel: 1, ..config }, &mut RejectHost),
        Err(Error::FuelExhausted)
    );
    p.define(main, |b, _| {
        b.loop_(&[], &[], |b, _| b.continue_(&[]));
        Terminator::UNREACHABLE
    });
    assert_eq!(
        evaluate(&p, main, &[], config, &mut RejectHost),
        Err(Error::FuelExhausted)
    );
}

struct TestHost {
    calls: Vec<String>,
}
impl Host for TestHost {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        self.calls.push(name.to_owned());
        match name {
            "argc" => Ok(HostResult::Return(vec![BigUint::from(7u8)])),
            "exit" => Ok(HostResult::Halt(args.to_vec())),
            _ => Err(Error::Host(name.to_owned())),
        }
    }
}

#[test]
fn deterministic_host_can_return_values_and_halt_callers() {
    let (mut p, main) = Program::new("main");
    let argc = p.platform("argc");
    let exit = p.platform("exit");
    let f = p.declare("stop", &[], &[]);
    p.define(f, |b, _| {
        let count = b.platform_call(argc, &[]);
        b.platform_call(exit, &count);
        Terminator::UNREACHABLE
    });
    p.define(main, |b, _| {
        b.call(f, &[]);
        Terminator::UNREACHABLE
    });
    for word_bits in [16, 32, 64] {
        let mut host = TestHost { calls: Vec::new() };
        let result = evaluate(
            &p,
            main,
            &[],
            Config {
                word_bits,
                ..Config::default()
            },
            &mut host,
        )
        .unwrap();
        assert_eq!(result.halted().unwrap(), vec![BigUint::from(7u8)]);
        assert_eq!(host.calls, ["argc", "exit"]);
    }
    assert!(matches!(run(&p, main, &[], 64), Err(Error::Host(_))));
}

#[test]
fn malformed_executed_ids_and_exit_arities_do_not_panic() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| b.ret(&[]));
    assert!(matches!(
        run(&p, main, &[], 64),
        Err(Error::InvalidProgram(_))
    ));
    assert!(matches!(
        run(&p, FunctionId(u32::MAX), &[], 64),
        Err(Error::InvalidProgram(_))
    ));
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 0);
        b.ret(&[value])
    });
    let op = p.regions[p.functions[main.index()].body.index()]
        .ops
        .range()
        .start;
    p.ops[op] = Op::Convert {
        class: Class::Word,
        value: ValueId(u32::MAX),
    };
    assert!(matches!(
        run(&p, main, &[], 64),
        Err(Error::InvalidProgram(_))
    ));
}

#[test]
fn return_crosses_nested_loops_without_running_the_continuation() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let answer = b.constant(Class::Word, 42);
        b.loop_(&[], &[], |b, _| {
            b.loop_(&[], &[], |b, _| b.ret(&[answer]));
            Terminator::UNREACHABLE
        });
        Terminator::UNREACHABLE
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(42u8)]
        );
    }
}

struct MemoryHost(Vec<u8>);
impl Host for MemoryHost {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        assert_eq!(name, "write");
        let address = u64::try_from(&args[0]).map_err(|_| Error::InvalidMemory)?;
        let len = usize::try_from(&args[1]).map_err(|_| Error::InvalidMemory)?;
        self.0.extend_from_slice(memory.read(address, len)?);
        Ok(HostResult::Return(Vec::new()))
    }
}

#[test]
fn host_observes_data_and_byte_stores_truncate_only_the_written_byte() {
    let (mut p, main) = Program::new("main");
    let data = p.intern(b"hello");
    let global = p.global(&[0; 2]);
    let write = p.platform("write");
    p.define(main, |b, _| {
        let address = b.address_of(data);
        let len = b.data_len(data);
        b.platform_call(write, &[address, len]);
        let address = b.address_of(global);
        let value = b.constant(Class::Word, 0x1234);
        b.store(Width::Byte, address, Offset::Bytes(1), value);
        b.ret(&[value])
    });
    for word_bits in [16, 32, 64] {
        let mut host = MemoryHost(Vec::new());
        let result = evaluate(
            &p,
            main,
            &[],
            Config {
                word_bits,
                ..Config::default()
            },
            &mut host,
        )
        .unwrap();
        assert_eq!(host.0, b"hello");
        assert_eq!(result.returned().unwrap(), vec![BigUint::from(0x1234u16)]);
        assert_eq!(result.globals, [0, 0x34]);
    }
}

fn binary_program(class: Class, op: Binary) -> (Program, FunctionId) {
    let (mut p, _) = Program::new("main");
    let f = p.declare("binary", &[class, class], &[class]);
    p.define(f, |b, args| {
        let result = b.binary(op, args[0], args[1]);
        b.ret(&[result])
    });
    (p, f)
}

#[test]
fn direct_unsigned_operations_match_word_model_including_wrap_and_zero() {
    for bits in [16, 32, 64] {
        let max = u64::MAX >> (64 - bits);
        let high = 1u64 << (bits - 1);
        for op in [Binary::Mul, Binary::Div, Binary::Mod] {
            let (p, f) = binary_program(Class::Word, op);
            for left in [0, 1, 2, 3, high, max] {
                for right in [0, 1, 2, 3, high, max] {
                    let expected = match op {
                        Binary::Mul => left.wrapping_mul(right) & max,
                        Binary::Div => left.checked_div(right).unwrap_or(0),
                        Binary::Mod => left.checked_rem(right).unwrap_or(left),
                        _ => unreachable!(),
                    };
                    assert_eq!(
                        run(&p, f, &[left, right], bits)
                            .unwrap()
                            .returned()
                            .unwrap(),
                        vec![BigUint::from(expected)],
                        "{op:?}({left},{right})/{bits}"
                    );
                }
            }
        }
    }
}

fn natural_model(op: Binary, left: &BigUint, right: &BigUint) -> BigUint {
    match op {
        Binary::Mul => left * right,
        Binary::Div => {
            if right == &BigUint::default() {
                BigUint::default()
            } else {
                left / right
            }
        }
        Binary::Mod => {
            if right == &BigUint::default() {
                left.clone()
            } else {
                left % right
            }
        }
        _ => unreachable!(),
    }
}

#[test]
fn direct_natural_operations_preserve_full_magnitudes_and_total_zero_semantics() {
    let large = (BigUint::from(1u8) << 200usize) + BigUint::from(17u8);
    let small = (BigUint::from(1u8) << 100usize) + BigUint::from(3u8);
    let cases = [
        BigUint::default(),
        BigUint::from(1u8),
        BigUint::from(u64::MAX),
        small,
        large,
    ];
    for op in [Binary::Mul, Binary::Div, Binary::Mod] {
        let (p, f) = binary_program(Class::Natural, op);
        for left in &cases {
            for right in &cases {
                let expected = natural_model(op, left, right);
                for word_bits in [16, 32, 64] {
                    let result = evaluate(
                        &p,
                        f,
                        &[left.clone(), right.clone()],
                        Config {
                            word_bits,
                            ..Config::default()
                        },
                        &mut RejectHost,
                    )
                    .unwrap();
                    assert_eq!(result.returned().unwrap(), vec![expected.clone()]);
                }
            }
        }
    }
}

#[test]
fn natural_multiplication_size_guard_accepts_exact_boundary_and_zero() {
    let (p, f) = binary_program(Class::Natural, Binary::Mul);
    let config = Config {
        max_natural_bits: 8,
        ..Config::default()
    };
    for (left, right, expected) in [(8u16, 16u16, 128u16), (0, 255, 0), (255, 1, 255)] {
        let result =
            evaluate(&p, f, &[left.into(), right.into()], config, &mut RejectHost).unwrap();
        assert_eq!(result.returned().unwrap(), vec![expected.into()]);
    }
    // 128*2 is known oversized from bit lengths alone. 15*31 has the
    // ambiguous bit-length boundary and fails the exact post-product check.
    for (left, right) in [(128u16, 2u16), (15, 31)] {
        assert_eq!(
            evaluate(&p, f, &[left.into(), right.into()], config, &mut RejectHost),
            Err(Error::SizeLimit)
        );
    }
    let large = BigUint::from(1u8) << 4095usize;
    assert_eq!(
        evaluate(
            &p,
            f,
            &[large.clone(), large],
            Config {
                max_natural_bits: 4096,
                ..config
            },
            &mut RejectHost
        ),
        Err(Error::SizeLimit)
    );
}

#[test]
fn fixed_products_require_a_fitting_result_class() {
    let class = Class::Fixed { bits: 8 };
    let (mut p, f) = binary_program(class, Binary::Mul);
    let wide = p.declare("wide", &[class, class], &[Class::Fixed { bits: 9 }]);
    p.define(wide, |b, args| {
        let product = b.binary_at(Class::Fixed { bits: 9 }, Binary::Mul, args[0], args[1]);
        b.ret(&[product])
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, f, &[15, 17], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(255u16)]
        );
        assert_eq!(run(&p, f, &[16, 16], bits), Err(Error::DoesNotFit(class)));
        assert_eq!(
            run(&p, wide, &[16, 16], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(256u16)]
        );
    }
}

#[test]
fn zero_bit_fixed_values_constants_and_conversions_are_always_zero() {
    let class = Class::Fixed { bits: 0 };
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(class, u64::MAX);
        let value = b.constant(Class::Word, 123);
        let converted = b.convert(class, value);
        let equal = b.compare(Relation::Equal, zero, converted);
        b.ret(&[equal])
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(1u8)]
        );
        for op in [
            Binary::Add,
            Binary::Sub,
            Binary::Mul,
            Binary::Div,
            Binary::Mod,
        ] {
            let (p, f) = binary_program(class, op);
            assert_eq!(
                run(&p, f, &[0, 0], bits).unwrap().returned().unwrap(),
                vec![BigUint::default()]
            );
            assert_eq!(run(&p, f, &[1, 0], bits), Err(Error::DoesNotFit(class)));
        }
    }
}

#[test]
fn oversized_word_and_address_constants_are_rejected_not_truncated() {
    let (mut p, main) = Program::new("main");
    for class in [Class::Word, Class::Address] {
        p.define(main, |b, _| {
            let max = b.constant(class, u64::MAX);
            let word = b.convert(Class::Word, max);
            b.ret(&[word])
        });
        for bits in [16, 32] {
            assert_eq!(run(&p, main, &[], bits), Err(Error::DoesNotFit(class)));
        }
        assert_eq!(
            run(&p, main, &[], 64).unwrap().returned().unwrap(),
            vec![BigUint::from(u64::MAX)]
        );
    }
    // Fixed constants are normalized by Builder, before any target sees them.
    p.define(main, |b, _| {
        let byte = b.constant(Class::Fixed { bits: 8 }, 256);
        b.ret(&[byte])
    });
    for bits in [16, 32, 64] {
        assert_eq!(
            run(&p, main, &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
    }
    let op = p.regions[p.functions[main.index()].body.index()]
        .ops
        .range()
        .start;
    p.ops[op] = Op::Constant {
        class: Class::Fixed { bits: 8 },
        value: 256,
    };
    assert_eq!(
        run(&p, main, &[], 64),
        Err(Error::DoesNotFit(Class::Fixed { bits: 8 }))
    );
}

#[test]
fn shared_native_backend_arithmetic_fixtures_agree_with_interpreter() {
    use crate::programs::{arithmetic, wraps_at_eight_bits};
    for bits in [16, 32, 64] {
        for op in [Binary::Mul, Binary::Div, Binary::Mod] {
            let p = arithmetic::boundaries(bits, op);
            validate(&p).unwrap();
            assert_eq!(
                run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
                vec![BigUint::default()]
            );
        }
        let p = arithmetic::odd_conversion();
        assert_eq!(
            run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::default()]
        );
        let p = wraps_at_eight_bits();
        assert_eq!(
            run(&p, p.entry(), &[], bits).unwrap().returned().unwrap(),
            vec![BigUint::from(4u8)]
        );
        let p = arithmetic::preserves_host_count();
        let result = evaluate(
            &p,
            p.entry(),
            &[],
            Config {
                word_bits: bits,
                ..Config::default()
            },
            &mut TestHost { calls: Vec::new() },
        )
        .unwrap();
        assert_eq!(result.returned().unwrap(), vec![BigUint::default()]);
    }
}

struct OversizedHost;
impl Host for OversizedHost {
    fn call(&mut self, _: &str, _: &[BigUint], _: &mut Memory<'_>) -> Result<HostResult, Error> {
        Ok(HostResult::Return(vec![BigUint::from(1u8) << 64usize]))
    }
}

#[test]
fn host_results_do_not_implicitly_fit_a_word() {
    let (mut p, main) = Program::new("main");
    let argc = p.platform("argc");
    p.define(main, |b, _| {
        let count = b.platform_call(argc, &[]);
        b.ret(&count)
    });
    for word_bits in [16, 32, 64] {
        assert_eq!(
            evaluate(
                &p,
                main,
                &[],
                Config {
                    word_bits,
                    ..Config::default()
                },
                &mut OversizedHost
            ),
            Err(Error::DoesNotFit(Class::Word))
        );
    }
}
