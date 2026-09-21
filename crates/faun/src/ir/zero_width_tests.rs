use super::{Class, Op, Program, Returns, evaluate, validate};
use crate::{barb::OptimizeOptions, platform::Routines};
use num_bigint::BigUint;

const SOURCE: &str = include_str!("../../tests/support/zero_width.fn");
const ZERO: Class = Class::Fixed { bits: 0 };
const BIT: Class = Class::Fixed { bits: 1 };

#[test]
fn zero_constants_choose_fixed0_but_the_entry_still_returns_a_word() {
    for word_bits in [16, 32, 64] {
        for (value, bits) in [(0, 0), (1, 1), (2, 2)] {
            let source = format!(
                "type Nat Zero Succ(Nat)\nmain!(h) -> exit!(h {}Zero{})",
                "Succ(".repeat(value),
                ")".repeat(value)
            );
            for constant_fold in [true, false] {
                let program = crate::read_with_options(
                    &source,
                    &Routines::builtin().with_word(word_bits),
                    &OptimizeOptions {
                        constant_fold,
                        ..OptimizeOptions::default()
                    },
                )
                .unwrap();
                validate(&program).unwrap();
                let entry = program.function(program.entry());
                assert_eq!(program.signature(entry.returns.classes()), [Class::Word]);
                let body = entry.body().unwrap();
                let Some(Op::Call { args, .. }) = program.ops(body).last() else {
                    panic!("the source ends with exit");
                };
                assert_eq!(program.values(*args).len(), 1);
                assert_eq!(
                    program.class(program.values(*args)[0]),
                    Class::Fixed { bits }
                );
            }
        }
    }
}

fn program(word_bits: u16, options: &OptimizeOptions) -> Program {
    let program =
        crate::read_with_options(SOURCE, &Routines::builtin().with_word(word_bits), options)
            .unwrap();
    validate(&program).unwrap();
    program
}

#[test]
fn zero_parameters_results_and_joins_are_not_erased() {
    for word_bits in [16, 32, 64] {
        let p = program(
            word_bits,
            &OptimizeOptions {
                inline_helpers: false,
                ..OptimizeOptions::default()
            },
        );
        for (name, params, result) in [
            ("keep_zero!", vec![ZERO], ZERO),
            ("select_zero!", vec![BIT], ZERO),
            ("zero_or_one", vec![BIT, ZERO], BIT),
        ] {
            let function = p
                .functions()
                .iter()
                .find(|f| p.name(f.name) == name)
                .unwrap();
            assert_eq!(p.signature(function.params), params, "{name}");
            let Returns::Values(results) = function.returns else {
                panic!("a scalar result")
            };
            assert_eq!(p.signature(results), [result], "{name}");
        }
        let has_join = |class| {
            p.regions.ids().any(|id| {
                p.walk(id).any(|(op, results)| {
                    matches!(op, Op::If { .. })
                        && results.len() == 1
                        && p.class(results[0]) == class
                })
            })
        };
        assert!(has_join(ZERO), "two zero-valued arms join as fixed0");
        assert!(
            has_join(BIT),
            "zero and one join at a width that holds both"
        );
    }
}

#[test]
fn range_proven_zero_arithmetic_selects_fixed0() {
    let source = format!(
        "{}\nmain!(h) ->\n  n = argc!(h)\n  exit!(h mod(n Succ(Zero)))",
        include_str!("../../../../standard/nat.fn")
    );
    for word_bits in [16, 32, 64] {
        let p = crate::read_with_options(
            &source,
            &Routines::builtin().with_word(word_bits),
            &OptimizeOptions {
                arithmetic_laws: false,
                ..OptimizeOptions::default()
            },
        )
        .unwrap();
        validate(&p).unwrap();
        let body = p.function(p.entry()).body().unwrap();
        assert!(p.every(body).any(|op| matches!(
            op,
            Op::Binary {
                op: super::Binary::Mod,
                ..
            }
        )));
        assert!(
            p.every(body)
                .any(|op| matches!(op, Op::Convert { class, .. } if *class == ZERO))
        );
        for argc in [0, 1, 255, 65535] {
            let mut host = Host {
                argc,
                ..Host::default()
            };
            let result = evaluate_entry(&p, word_bits, &mut host);
            assert_eq!(result.halted().unwrap(), [BigUint::from(0u8)]);
            assert_eq!(host.calls, ["argc!", "exit!"]);
        }
    }
}

fn comparison_program(word_bits: u16, constructors: &str, expression: &str) -> Program {
    let library = include_str!("../../../../standard/nat.fn")
        .replace("type Bool False True", &format!("type Bool {constructors}"));
    let source = format!(
        "{library}\nprobe(n) -> {expression}\n\
         status!(h False) -> exit!(h Zero)\n\
         status!(h True) -> exit!(h Succ(Zero))\n\
         main!(h) ->\n  n = argc!(h)\n  status!(h probe(n))"
    );
    let p = crate::read_with_options(
        &source,
        &Routines::builtin().with_word(word_bits),
        &OptimizeOptions {
            arithmetic_laws: false,
            constant_fold: false,
            ..OptimizeOptions::default()
        },
    )
    .unwrap();
    validate(&p).unwrap();
    p
}

fn comparison_arms(p: &Program, yes_tag: u64) {
    let body = p.function(p.entry()).body().unwrap();
    let (yes, no, result) = p
        .walk(body)
        .find_map(|(op, results)| match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } => Some((then_region, else_region, results[0])),
            _ => None,
        })
        .expect("a comparison materialized as a tagged result");
    assert_eq!(
        p.class(result),
        BIT,
        "the join must hold either emitted tag"
    );
    for (arm, tag) in [(yes, yes_tag), (no, 1 - yes_tag)] {
        let (op, results) = p.walk(arm).next().unwrap();
        let class = if tag == 0 { ZERO } else { BIT };
        assert_eq!(*op, Op::Constant { class, value: tag });
        assert_eq!(p.class(results[0]), class);
        assert_eq!(
            p.outgoing(arm),
            results,
            "yield the narrow constant directly"
        );
    }
}

#[test]
fn comparison_arms_use_minimal_constants_and_a_wide_enough_join() {
    for word_bits in [16, 32, 64] {
        for (constructors, yes_tag) in [("False True", 1), ("True False", 0)] {
            for (expression, answers, known) in [
                ("equals(n Succ(Zero))", [0u8, 1, 0, 0], None),
                ("less_than(n Succ(Zero))", [1, 0, 0, 0], None),
                ("equals(mod(n Succ(Zero)) Zero)", [1, 1, 1, 1], Some(true)),
                ("less_than(n Zero)", [0, 0, 0, 0], Some(false)),
            ] {
                let p = comparison_program(word_bits, constructors, expression);
                comparison_arms(&p, yes_tag);
                if known.is_some_and(|yes| if yes { yes_tag == 0 } else { yes_tag == 1 }) {
                    let body = p.function(p.entry()).body().unwrap();
                    assert!(
                        p.every(body)
                            .any(|op| matches!(op, Op::Convert { class, .. } if *class == ZERO)),
                        "a proven zero is narrowed after the join"
                    );
                }
                for (argc, answer) in [0, 1, 2, 33].into_iter().zip(answers) {
                    let mut host = Host {
                        argc,
                        ..Host::default()
                    };
                    let result = evaluate_entry(&p, word_bits, &mut host);
                    assert_eq!(
                        result.halted().unwrap(),
                        [BigUint::from(answer)],
                        "{constructors}: {expression}, argc={argc}"
                    );
                    assert_eq!(host.calls, ["argc!", "exit!"]);
                }
            }
        }
    }
}

fn evaluate_entry(p: &Program, word_bits: u16, host: &mut Host) -> evaluate::Evaluation {
    evaluate::evaluate(
        p,
        p.entry(),
        &[],
        evaluate::Config {
            word_bits,
            ..evaluate::Config::default()
        },
        host,
    )
    .unwrap()
}

#[derive(Default)]
struct Host {
    argc: u16,
    calls: Vec<String>,
    halt_on_read: Option<usize>,
}

impl evaluate::Host for Host {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut evaluate::Memory<'_>,
    ) -> Result<evaluate::HostResult, evaluate::Error> {
        self.calls.push(name.to_owned());
        match name {
            "argc!" if self.halt_on_read == Some(self.calls.len()) => {
                Ok(evaluate::HostResult::Halt(vec![BigUint::from(7u8)]))
            }
            "argc!" => Ok(evaluate::HostResult::Return(vec![BigUint::from(self.argc)])),
            "exit!" => Ok(evaluate::HostResult::Halt(args.to_vec())),
            _ => Err(evaluate::Error::Host(name.to_owned())),
        }
    }
}

#[test]
fn zero_results_preserve_eager_calls_and_nonreturning_execution() {
    for word_bits in [16, 32, 64] {
        for inline_helpers in [true, false] {
            let p = program(
                word_bits,
                &OptimizeOptions {
                    inline_helpers,
                    ..OptimizeOptions::default()
                },
            );
            for argc in [1, 2, 33] {
                for halt_on_read in [None, Some(2)] {
                    let mut host = Host {
                        argc,
                        halt_on_read,
                        ..Host::default()
                    };
                    let result = evaluate_entry(&p, word_bits, &mut host);
                    let (answer, calls): (u8, &[&str]) = if halt_on_read.is_some() {
                        (7, &["argc!", "argc!"])
                    } else {
                        (u8::from(argc == 1), &["argc!", "argc!", "exit!"])
                    };
                    assert_eq!(result.halted().unwrap(), [BigUint::from(answer)]);
                    assert_eq!(host.calls, calls);
                }
            }
        }
    }
}
