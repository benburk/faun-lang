//! Representation and ownership tests use the scalar memory interpreter, not
//! only low exit statuses. Runtime inputs are parameters, never folded terms.
use num_bigint::BigUint;

use super::evaluate::{self, Evaluation, Host, HostResult, Memory};
use super::natural::Config;
use super::test_support::{no_live_objects, word};
use super::*;

#[test]
#[expect(
    clippy::redundant_closure_for_method_calls,
    reason = "the builder method is not lifetime-general enough as a direct callback"
)]
fn nested_cells_are_legalized_to_managed_objects_and_released() {
    let (mut source, main) = Program::new("main");
    let identity = source.declare("identity", &[Class::Cell], &[Class::Cell]);
    source.define(identity, |b, params| b.ret(params));
    source.define(main, |b, _| {
        let answer = b.constant(Class::Word, 42);
        let inner = b.cell(7, &[answer]);
        let outer = b.cell(3, &[inner]);
        let returned = b.call_one(identity, &[outer]);
        let projected = b.cell_field(Class::Cell, returned, 0);
        let result = b.cell_field(Class::Word, projected, 0);
        b.ret(&[result]);
    });
    let config = Config {
        word_bits: 64,
        heap_bytes: 512,
    };
    let legalized = legalize(&source, config).unwrap();
    assert!(legalized.ops.iter().all(|op| !matches!(
        op,
        Op::Cell { .. } | Op::CellTag { .. } | Op::CellField { .. }
    )));
    let evaluation = run(&legalized, main, &[], 64);
    assert_eq!(evaluation.returned().unwrap(), &[BigUint::from(42u8)]);
    no_live_objects(&legalized, &evaluation, config);
}

/// A managed field is not always a scalar: a cell holding an
/// arbitrary-precision natural has to retain and release that field the way
/// it retains and releases a nested cell.
#[test]
fn a_cell_holding_a_natural_retains_and_releases_that_field() {
    let (mut source, main) = Program::new("main");
    source.define(main, |b, _| {
        let word = b.constant(Class::Word, 42);
        let counted = b.convert(Class::Natural, word);
        let cell = b.cell(1, &[counted]);
        let field = b.cell_field(Class::Natural, cell, 0);
        let answer = b.convert(Class::Word, field);
        b.ret(&[answer]);
    });
    let config = Config {
        word_bits: 64,
        heap_bytes: 512,
    };
    let legalized = legalize(&source, config).unwrap();
    let evaluation = run(&legalized, main, &[], 64);
    assert_eq!(evaluation.returned().unwrap(), &[BigUint::from(42u8)]);
    no_live_objects(&legalized, &evaluation, config);
}

#[derive(Default)]
struct TestHost {
    calls: Vec<String>,
}

impl Host for TestHost {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut Memory<'_>,
    ) -> Result<HostResult, evaluate::Error> {
        self.calls.push(name.to_owned());
        if name == "exit!" {
            Ok(HostResult::Halt(args.to_vec()))
        } else if name == "mark" {
            Ok(HostResult::Return(vec![]))
        } else {
            Err(evaluate::Error::Host(name.to_owned()))
        }
    }
}

fn run(p: &Program, f: FunctionId, args: &[BigUint], word_bits: u16) -> Evaluation {
    evaluate::evaluate(
        p,
        f,
        args,
        evaluate::Config {
            word_bits,
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut TestHost::default(),
    )
    .expect("reference execution")
}

fn base() -> (Program, FunctionId) {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let test = p.declare("test", &[Class::Word], &[Class::Natural]);
    (p, test)
}

fn decoded(p: &Program, evaluation: &Evaluation, bits: u16) -> BigUint {
    let address = word(&evaluation.returned().unwrap()[0].to_bytes_le());
    let globals = p.data().len() + 2;
    let (bytes, start) = if address >= globals {
        (&evaluation.globals[..], address - globals)
    } else {
        (p.data(), address - 1)
    };
    let w = usize::from(bits / 8);
    let len = word(&bytes[start + 2 * w..start + 3 * w]);
    let digits = &bytes[start + 3 * w..start + 3 * w + len];
    assert!(digits.last().is_none_or(|&byte| byte != 0), "normalized");
    if address >= globals {
        assert_eq!(
            word(&bytes[start + w..start + 2 * w]),
            1,
            "one returned claim"
        );
    }
    BigUint::from_bytes_le(digits)
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "differential fixture and its width/operation/input matrix"
)]
fn exact_runtime_arithmetic_and_returned_ownership_at_each_word_size() {
    for bits in [16, 32, 64] {
        for operation in [
            Binary::Add,
            Binary::Sub,
            Binary::Mul,
            Binary::Div,
            Binary::Mod,
        ] {
            let (mut p, test) = base();
            let arithmetic = p.declare(
                "arithmetic",
                &[Class::Natural, Class::Natural],
                &[Class::Natural],
            );
            p.define(arithmetic, |b, a| {
                let result = b.binary(operation, a[0], a[1]);
                b.ret(&[result]);
            });
            p.define(test, |b, a| {
                let input = b.convert(Class::Natural, a[0]);
                let large = b.natural(&((BigUint::from(1u8) << 100usize) + BigUint::from(255u16)));
                let left = b.binary(Binary::Add, large, input);
                let divisor = b.constant(Class::Natural, 257);
                let right = b.binary(Binary::Add, divisor, input);
                let result = b.call(arithmetic, &[left, right]);
                b.ret(&result);
            });
            let config = Config {
                word_bits: bits,
                heap_bytes: 2048,
            };
            let scalar = legalize(&p, config).expect("legalized");
            assert!(
                (0..scalar.values_count())
                    .all(|at| scalar.class(ValueId::at(at)) != Class::Natural)
            );
            for seed in [0u64, 1, 255, 4095] {
                let args = [BigUint::from(seed)];
                let expected = run(&p, test, &args, bits);
                let actual = run(&scalar, test, &args, bits);
                assert!(actual.returned().is_some());
                assert_eq!(
                    decoded(&scalar, &actual, bits),
                    expected.returned().unwrap()[0],
                    "{bits} {operation:?} {seed}"
                );
            }
        }
    }
}

#[test]
fn zero_division_and_monus_alias_paths_keep_returned_values_live() {
    for bits in [16, 32, 64] {
        for operation in [Binary::Sub, Binary::Div, Binary::Mod] {
            for zero_right in [true, false] {
                let (mut p, test) = base();
                p.define(test, |b, a| {
                    let input = b.convert(Class::Natural, a[0]);
                    let right = if zero_right {
                        b.constant(Class::Natural, 0)
                    } else {
                        input
                    };
                    let result = b.binary(operation, input, right);
                    b.ret(&[result]);
                });
                let scalar = legalize(
                    &p,
                    Config {
                        word_bits: bits,
                        heap_bytes: 256,
                    },
                )
                .unwrap();
                let args = [BigUint::from(65535u32)];
                let expected = run(&p, test, &args, bits);
                let actual = run(&scalar, test, &args, bits);
                assert_eq!(
                    decoded(&scalar, &actual, bits),
                    expected.returned().unwrap()[0]
                );
            }
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "nested control-flow fixture is clearest as a single graph"
)]
fn lifetime_program(early_return: bool) -> (Program, FunctionId) {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let pair = p.declare(
        "duplicate borrowed",
        &[Class::Natural],
        &[Class::Natural, Class::Natural],
    );
    p.define(pair, |b, a| b.ret(&[a[0], a[0]]));
    let test = p.declare("lifetime", &[Class::Word], &[Class::Word]);
    p.define(test, |b, args| {
        let ancestor = b.convert(Class::Natural, args[0]);
        let pair = b.call(pair, &[ancestor]);
        let zero = b.constant(Class::Word, 0);
        let result = b.loop_(
            &[pair[0], pair[1], zero],
            &[Class::Natural, Class::Natural],
            |b, state| {
                let one = b.constant(Class::Natural, 1);
                let next = b.binary(Binary::Add, state[0], one);
                let inner = b.loop_(&[next, zero], &[Class::Natural], |b, carried| {
                    let first = b.compare(Relation::Equal, carried[1], zero);
                    b.if_(
                        first,
                        &[],
                        |b| {
                            let one = b.constant(Class::Word, 1);
                            b.continue_(&[carried[0], one]);
                        },
                        |b| b.yield_(&[]),
                    );
                    let three = b.constant(Class::Word, 3);
                    let stop = if early_return {
                        b.compare(Relation::Equal, state[2], three)
                    } else {
                        b.constant(Class::Word, 0)
                    };
                    b.if_(
                        stop,
                        &[],
                        |b| {
                            let old = b.convert(Class::Word, ancestor);
                            b.ret(&[old]);
                        },
                        |b| b.break_(&[carried[0]]),
                    );
                });
                let more = b.compare(Relation::Less, state[2], args[0]);
                b.if_(
                    more,
                    &[],
                    |b| {
                        let one = b.constant(Class::Word, 1);
                        let index = b.binary(Binary::Add, state[2], one);
                        b.continue_(&[state[1], inner[0], index]);
                    },
                    |b| b.break_(&[inner[0], inner[0]]),
                );
            },
        );
        let sum = b.binary(Binary::Add, result[0], result[1]);
        let status = b.convert(Class::Word, sum);
        b.ret(&[status]);
    });
    (p, test)
}

#[test]
fn loops_rotate_aliases_reuse_tiny_heaps_and_clean_nested_early_returns() {
    for bits in [16, 32, 64] {
        for early in [false, true] {
            let (p, test) = lifetime_program(early);
            let config = Config {
                word_bits: bits,
                heap_bytes: 512,
            };
            let scalar = legalize(&p, config).unwrap();
            for seed in [0u64, 3, 200] {
                let args = [BigUint::from(seed)];
                let expected = run(&p, test, &args, bits);
                let actual = run(&scalar, test, &args, bits);
                assert_eq!(actual.outcome, expected.outcome);
                no_live_objects(&scalar, &actual, config);
            }
        }
    }
}

#[test]
fn recursive_calls_borrow_parameters_and_transfer_owned_results() {
    for bits in [16, 32, 64] {
        let (mut p, main) = Program::new("main");
        let recurse = p.declare("recurse", &[Class::Word, Class::Natural], &[Class::Natural]);
        p.define(recurse, |b, args| {
            let zero = b.constant(Class::Word, 0);
            let done = b.compare(Relation::Equal, args[0], zero);
            b.if_(
                done,
                &[],
                |b| b.ret(&[args[1]]),
                |b| {
                    let one = b.constant(Class::Natural, 1);
                    let next = b.binary(Binary::Add, args[1], one);
                    let one = b.constant(Class::Word, 1);
                    let count = b.binary(Binary::Sub, args[0], one);
                    let inner = b.call_one(recurse, &[count, next]);
                    // Reading a borrowed parameter after the recursive call must
                    // remain safe even if the callee reuses released heap blocks.
                    let result = b.binary(Binary::Add, inner, args[1]);
                    b.ret(&[result]);
                },
            );
        });
        p.define(main, |b, _| {
            let word = b.constant(Class::Word, 7);
            let input = b.convert(Class::Natural, word);
            let count = b.constant(Class::Word, 12);
            let value = b.call_one(recurse, &[count, input]);
            let result = b.convert(Class::Word, value);
            b.ret(&[result]);
        });
        let config = Config {
            word_bits: bits,
            heap_bytes: 1024,
        };
        let scalar = legalize(&p, config).unwrap();
        let expected = run(&p, main, &[], bits);
        let actual = run(&scalar, main, &[], bits);
        assert_eq!(actual.outcome, expected.outcome);
        no_live_objects(&scalar, &actual, config);
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "conversion graph and cross-width differential matrix"
)]
fn conversion_aliases_comparisons_and_odd_width_truncation() {
    for bits in [16, 32, 64] {
        for narrow in [0, 1, 7, 8, 9, 15, 16, 31, 32, 63, 64]
            .into_iter()
            .filter(|&n| n <= bits)
        {
            let (mut p, main) = Program::new("main");
            let test = p.declare("conversions", &[Class::Word], &[Class::Word]);
            p.define(main, |b, _| {
                let zero = b.constant(Class::Word, 0);
                b.ret(&[zero]);
            });
            p.define(test, |b, args| {
                let a = b.convert(Class::Natural, args[0]);
                let alias = b.convert(Class::Natural, a);
                let equal = b.compare(Relation::Equal, a, alias);
                let zero = b.constant(Class::Natural, 0);
                let positive = b.compare(Relation::Less, zero, alias);
                let result = b.if_(
                    positive,
                    &[Class::Natural],
                    |b| {
                        let high = b.natural(&(BigUint::from(1u8) << 100usize));
                        let value = b.binary(Binary::Add, alias, high);
                        b.yield_(&[value]);
                    },
                    |b| b.yield_(&[zero]),
                );
                let narrow = b.convert(Class::fixed(narrow), result[0]);
                let result = b.convert(Class::Word, narrow);
                let result = b.binary(Binary::Mul, result, equal);
                b.ret(&[result]);
            });
            let config = Config {
                word_bits: bits,
                heap_bytes: 256,
            };
            let scalar = legalize(&p, config).unwrap();
            for seed in [0u64, 255, 256, 65535, u64::MAX >> (64 - bits)] {
                let args = [BigUint::from(seed)];
                let expected = run(&p, test, &args, bits);
                let actual = run(&scalar, test, &args, bits);
                assert_eq!(actual.outcome, expected.outcome);
                no_live_objects(&scalar, &actual, config);
            }
        }
    }
}

#[test]
fn pools_effects_and_nonreturning_platform_boundaries_are_preserved() {
    let (mut p, main) = Program::new("main");
    let data = p.intern(b"unaligned");
    let global = p.global(&[7, 8, 9]);
    let exit = crate::platform::Routines::builtin().declare(&mut p, "exit!");
    p.define(main, |b, _| {
        b.address_of(data);
        b.address_of(global);
        let value = b.constant(Class::Word, 42);
        b.convert(Class::Natural, value);
        b.call(exit, &[value]);
    });
    let scalar = legalize(
        &p,
        Config {
            word_bits: 64,
            heap_bytes: 256,
        },
    )
    .unwrap();
    assert_eq!(&scalar.data()[..p.data().len()], p.data());
    assert_eq!(&scalar.globals()[..p.globals().len()], p.globals());
    assert_eq!(
        &scalar.spans.as_slice()[..p.spans.len()],
        p.spans.as_slice()
    );
    assert_eq!(
        scalar.function(exit).definition,
        p.function(exit).definition
    );
    assert_eq!(scalar.function(exit).returns, Returns::Never);
    let ops = scalar.ops(scalar.function(scalar.entry()).body().unwrap());
    assert!(matches!(ops.last(), Some(Op::Call { function, .. }) if *function == exit));
    let mut host = TestHost::default();
    let result =
        evaluate::evaluate(&scalar, main, &[], evaluate::Config::default(), &mut host).unwrap();
    assert_eq!(result.halted().unwrap(), [BigUint::from(42u8)]);
    assert_eq!(host.calls, ["exit!"]);
}

#[test]
fn unsupported_representations_are_errors_not_pointer_reinterpretations() {
    for (source, target) in [
        (Class::Address, Class::Natural),
        (Class::Natural, Class::Address),
    ] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let value = b.constant(source, 1);
            b.convert(target, value);
            let zero = b.constant(Class::Word, 0);
            b.ret(&[zero]);
        });
        assert!(
            legalize(
                &p,
                Config {
                    word_bits: 64,
                    heap_bytes: 256
                }
            )
            .is_err()
        );
    }
    let (mut p, main) = Program::new("main");
    // Wider than the machine, which is a program this cannot represent
    // rather than one it can hold. Nothing above can write a width no
    // number needs, so the width said here is one a smaller machine has
    // not got.
    p.define(main, |b, _| {
        b.constant(Class::fixed(17), 1);
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    assert!(
        legalize(
            &p,
            Config {
                word_bits: 16,
                heap_bytes: 256
            }
        )
        .unwrap_err()
        .contains("Fixed")
    );
}

#[test]
fn natural_host_signatures_do_not_become_address_signatures() {
    let mut routines = crate::platform::Routines::builtin();
    routines.push(crate::platform::Routine {
        name: "foreign".into(),
        offered: false,
        takes: vec![crate::platform::Takes::Scalar(Class::Natural)],
        returns: crate::platform::Returns::Value(Class::Natural),
    });
    let (mut p, main) = Program::new("main");
    let foreign = routines.declare(&mut p, "foreign");
    p.define(main, |b, _| {
        let natural = b.constant(Class::Natural, 1);
        b.call(foreign, &[natural]);
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let error = legalize(
        &p,
        Config {
            word_bits: 64,
            heap_bytes: 256,
        },
    )
    .unwrap_err();
    assert!(error.contains("bigint ABI"), "{error}");
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "host setup, allocation fixture and observed failure ordering"
)]
fn exhaustion_preserves_effect_order_and_exits_instead_of_returning_zero() {
    for bits in [16, 32, 64] {
        let mut routines = crate::platform::Routines::builtin();
        routines.push(crate::platform::Routine {
            name: "mark".into(),
            offered: false,
            takes: vec![],
            returns: crate::platform::Returns::Unit,
        });
        let (mut p, main) = Program::new("main");
        let mark = routines.declare(&mut p, "mark");
        p.define(main, |b, _| {
            b.call(mark, &[]);
            let word = b.constant(Class::Word, 100);
            b.convert(Class::Natural, word);
            b.convert(Class::Natural, word);
            b.call(mark, &[]);
            b.ret(&[word]);
        });
        let scalar = legalize(
            &p,
            Config {
                word_bits: bits,
                heap_bytes: usize::from(bits / 8) * 4,
            },
        )
        .unwrap();
        let mut host = TestHost::default();
        let result = evaluate::evaluate(
            &scalar,
            main,
            &[],
            evaluate::Config {
                word_bits: bits,
                ..evaluate::Config::default()
            },
            &mut host,
        )
        .unwrap();
        assert_eq!(result.halted().unwrap(), [BigUint::from(2u8)]);
        assert_eq!(host.calls, ["mark", "exit!"]);
    }
}

#[test]
fn source_host_arguments_are_not_implicitly_truncated() {
    let source = "type Nat Zero Succ(Nat)\n\
        add(Zero b) -> b\n\
        add(Succ(a) b) -> Succ(add(a b))\n\
        main!(h) -> n = argc!(h) exit!(h add(n n))";
    let error =
        crate::read(source, &crate::platform::Routines::builtin().with_word(64)).unwrap_err();
    assert!(
        error.contains("host arguments must be proven to fit"),
        "{error}"
    );
    crate::read(
        "type Nat Zero Succ(Nat) main!(h) -> exit!(h Succ(Zero))",
        &crate::platform::Routines::builtin().with_word(16),
    )
    .unwrap();
}

#[test]
fn scalar_fast_path_has_no_runtime_code_data_or_globals() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let answer = b.constant(Class::Word, 42);
        b.ret(&[answer]);
    });
    let scalar = legalize(
        &p,
        Config {
            word_bits: 64,
            heap_bytes: 0,
        },
    )
    .unwrap();
    assert_eq!(format!("{p:?}"), format!("{scalar:?}"));
}
