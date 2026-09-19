use num_bigint::BigUint;

use super::evaluate::{self, Evaluation, Host, HostResult, Memory};
use super::natural::{self, Config, Library, Needs};
use super::{Binary, Builder, Class, DataId, FunctionId, Op, Program, Relation};
use crate::platform::{Routine, Routines};

const WORD: Class = Class::Word;
const ADDRESS: Class = Class::Address;

#[derive(Default)]
struct Observer {
    word: usize,
    seen: Vec<BigUint>,
}

fn read_word(bytes: &[u8]) -> u64 {
    let mut held = [0; 8];
    held[..bytes.len()].copy_from_slice(bytes);
    u64::from_le_bytes(held)
}

impl Host for Observer {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, evaluate::Error> {
        match name {
            "exit" => Ok(HostResult::Halt(args.to_vec())),
            "observe" => {
                let address = args[0].to_u64_digits()[0];
                let header = memory.read(address, 3 * self.word)?;
                let size = read_word(&header[..self.word]);
                let refs = read_word(&header[self.word..2 * self.word]);
                let len = read_word(&header[2 * self.word..]);
                assert!(refs > 0, "observing a released result");
                assert!(len + u64::try_from(3 * self.word).unwrap() <= size);
                let digits = memory.read(
                    address + u64::try_from(3 * self.word).unwrap(),
                    usize::try_from(len).unwrap(),
                )?;
                assert!(
                    digits.is_empty() || digits.last() != Some(&0),
                    "normalized result"
                );
                self.seen.push(BigUint::from_bytes_le(digits));
                Ok(HostResult::Return(vec![]))
            }
            _ => Err(evaluate::Error::Host(name.to_owned())),
        }
    }
}

fn program(config: Config, needs: Needs) -> (Program, Library, FunctionId) {
    let mut routines = Routines::builtin();
    routines.push(Routine {
        name: "observe".to_owned(),
        called: None,
        takes: vec![ADDRESS],
        answers: None,
        comes_back: true,
    });
    let (mut p, entry) = Program::with("test", routines);
    p.define(entry, |b, _| {
        let zero = b.constant(WORD, 0);
        b.ret(&[zero])
    });
    let lib = natural::append(&mut p, config, needs).unwrap();
    (p, lib, entry)
}

fn config(bits: u16) -> Config {
    Config {
        word_bits: bits,
        heap_bytes: 4096,
    }
}

fn run(
    p: &Program,
    function: FunctionId,
    args: &[BigUint],
    bits: u16,
) -> (Evaluation, Vec<BigUint>) {
    super::validate(p).unwrap();
    let mut host = Observer {
        word: usize::from(bits / 8),
        ..Observer::default()
    };
    let evaluation = evaluate::evaluate(
        p,
        function,
        args,
        evaluate::Config {
            word_bits: bits,
            fuel: 20_000_000,
            ..evaluate::Config::default()
        },
        &mut host,
    )
    .unwrap();
    (evaluation, host.seen)
}

fn free_heap(globals: &[u8], word: usize) {
    let mut cursor = 0;
    while cursor < globals.len() {
        let size = usize::try_from(read_word(&globals[cursor..cursor + word])).unwrap();
        assert!(size >= 4 * word && size.is_multiple_of(word));
        assert!(cursor + size <= globals.len());
        assert_eq!(
            read_word(&globals[cursor + word..cursor + 2 * word]),
            0,
            "unreleased allocation at {cursor}"
        );
        cursor += size;
    }
    assert_eq!(cursor, globals.len());
}

fn data_address(p: &Program, datum: DataId) -> BigUint {
    BigUint::from(u64::from(p.datum(datum).start) + 1)
}

fn observe_and_release(
    b: &mut Builder<'_>,
    lib: &Library,
    observer: super::PlatformId,
    value: super::ValueId,
) {
    b.platform_call(observer, &[value]);
    b.call(lib.release, &[value]);
}

#[test]
fn static_layout_configuration_and_pruning() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let word = usize::from(bits / 8);
        let (mut p, lib, _) = program(conf, Needs::default());
        assert!(p.globals().is_empty(), "no allocation family requested");
        assert_eq!(
            p.functions().len(),
            4,
            "entry, failure, retain, release only"
        );
        let magnitude = (BigUint::from(1u8) << 130usize) + BigUint::from(257u32);
        let datum = natural::constant(&mut p, conf, &magnitude).unwrap();
        for (datum, expected) in [(lib.zero, BigUint::default()), (datum, magnitude)] {
            let span = p.datum(datum);
            let bytes = &p.data()[usize::try_from(span.start).unwrap()
                ..usize::try_from(span.start + span.len).unwrap()];
            assert_eq!(read_word(&bytes[..word]), u64::from(span.len));
            assert_eq!(read_word(&bytes[word..2 * word]), u64::MAX >> (64 - bits));
            let len = usize::try_from(read_word(&bytes[2 * word..3 * word])).unwrap();
            assert_eq!(
                BigUint::from_bytes_le(&bytes[3 * word..3 * word + len]),
                expected
            );
        }
    }
}

#[test]
fn unused_arithmetic_families_are_not_generated() {
    for bits in [16, 32, 64] {
        let (p, _, _) = program(
            config(bits),
            Needs {
                add: true,
                ..Needs::default()
            },
        );
        let names: Vec<_> = p.functions().iter().map(|f| p.name(f.name)).collect();
        assert!(names.contains(&"nat.add"));
        assert!(!names.contains(&"nat.mul"));
        assert!(!names.contains(&"nat.divmod"));
        assert!(!names.contains(&"nat.compare"));
        assert!(!names.contains(&"nat.from_word"));
    }
}

#[test]
fn invalid_configurations_are_rejected() {
    for conf in [
        Config {
            word_bits: 8,
            heap_bytes: 64,
        },
        Config {
            word_bits: 16,
            heap_bytes: 7,
        },
        Config {
            word_bits: 16,
            heap_bytes: 65536,
        },
        Config {
            word_bits: 32,
            heap_bytes: 17,
        },
    ] {
        let (mut p, _) = Program::new("bad");
        assert!(natural::append(&mut p, conf, Needs::default()).is_err());
        assert!(natural::constant(&mut p, conf, &BigUint::default()).is_err());
    }
}

#[test]
fn generated_regions_fit_the_narrow_calling_convention() {
    for bits in [16, 32, 64] {
        let (p, _, _) = program(
            config(bits),
            Needs {
                add: true,
                sub: true,
                mul: true,
                div: true,
                modulo: true,
                compare: true,
                from_word: true,
                to_word: true,
            },
        );
        super::validate(&p).unwrap();
        for f in p.functions() {
            assert!(f.params.len() <= 4);
            assert!(f.returns.len() <= 1);
            assert!(
                region_values(&p, f.body) <= 128,
                "{} fits frame slots",
                p.name(f.name)
            );
            for op in p.every(f.body) {
                match *op {
                    Op::Loop { body, initial } => {
                        assert!(initial.len() <= 2);
                        assert!(p.region(body).params.len() <= 2);
                    }
                    Op::Call { args, .. } => assert!(args.len() <= 4),
                    _ => {}
                }
            }
        }
    }
}

fn region_values(p: &Program, region: super::RegionId) -> usize {
    p.region(region).params.len()
        + p.walk(region)
            .map(|(op, results)| {
                results.len()
                    + match *op {
                        Op::If {
                            then_region,
                            else_region,
                            ..
                        } => region_values(p, then_region) + region_values(p, else_region),
                        Op::Loop { body, .. } => region_values(p, body),
                        _ => 0,
                    }
            })
            .sum::<usize>()
}

fn samples(bits: u16) -> Vec<(BigUint, BigUint)> {
    let n = |n: u64| BigUint::from(n);
    let max = (n(1) << usize::from(bits)) - n(1);
    let huge = (n(1) << 160usize) - n(1);
    let mut pairs = vec![
        (n(0), n(0)),
        (n(1), n(0)),
        (n(0), n(7)),
        (n(1), n(1)),
        (n(255), n(1)),
        (n(256), n(255)),
        (n(255), n(257)),
        (max.clone(), n(1)),
        (max.clone(), max),
        (huge.clone(), n(257)),
        (huge.clone(), huge),
        ((n(1) << 128usize) + n(1), (n(1) << 65usize) + n(3)),
    ];
    let mut seed = 0x917d_5a32_0ed6_c41bu64;
    for _ in 0..12 {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let a = seed;
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        pairs.push((n(a), n(seed)));
    }
    pairs
}

#[test]
fn all_arithmetic_matches_biguint_at_every_word_width() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(
            conf,
            Needs {
                add: true,
                sub: true,
                mul: true,
                div: true,
                modulo: true,
                ..Needs::default()
            },
        );
        let checks = arithmetic_checks(&mut p, &lib);
        let pairs: Vec<_> = samples(bits)
            .into_iter()
            .map(|(a, c)| {
                let da = natural::constant(&mut p, conf, &a).unwrap();
                let dc = natural::constant(&mut p, conf, &c).unwrap();
                (a, c, da, dc)
            })
            .collect();
        for (op, check) in checks {
            for (a, c, da, dc) in &pairs {
                let expected = model(op, a, c);
                let args = [data_address(&p, *da), data_address(&p, *dc)];
                let (evaluation, seen) = run(&p, check, &args, bits);
                assert!(!evaluation.halted, "{bits} {op:?} {a} {c}");
                assert_eq!(
                    seen,
                    [expected, a.clone(), c.clone()],
                    "{bits} {op:?} {a} {c}"
                );
                free_heap(&evaluation.globals, usize::from(bits / 8));
            }
        }
    }
}

fn arithmetic_checks(p: &mut Program, lib: &Library) -> Vec<(Binary, FunctionId)> {
    let observer = p.platform("observe");
    [
        (Binary::Add, lib.add),
        (Binary::Sub, lib.sub),
        (Binary::Mul, lib.mul),
        (Binary::Div, lib.div),
        (Binary::Mod, lib.modulo),
    ]
    .into_iter()
    .map(|(op, function)| {
        let check = p.declare("check", &[ADDRESS, ADDRESS], &[WORD]);
        p.define(check, |b, args| {
            let out = b.call(function.unwrap(), args)[0];
            observe_and_release(b, lib, observer, out);
            // Arithmetic borrows rather than consumes or mutates operands.
            b.platform_call(observer, &[args[0]]);
            b.platform_call(observer, &[args[1]]);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero])
        });
        (op, check)
    })
    .collect()
}

fn model(op: Binary, a: &BigUint, c: &BigUint) -> BigUint {
    match op {
        Binary::Add => a + c,
        Binary::Sub if a < c => BigUint::default(),
        Binary::Sub => a - c,
        Binary::Mul => a * c,
        Binary::Div if c == &BigUint::default() => BigUint::default(),
        Binary::Div => a / c,
        Binary::Mod if c == &BigUint::default() => a.clone(),
        Binary::Mod => a % c,
    }
}

#[test]
fn comparison_and_explicit_low_word_conversion() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(
            conf,
            Needs {
                compare: true,
                to_word: true,
                ..Needs::default()
            },
        );
        assert!(p.globals().is_empty());
        let mask = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        for (a, c) in samples(bits) {
            let da = natural::constant(&mut p, conf, &a).unwrap();
            let dc = natural::constant(&mut p, conf, &c).unwrap();
            let (answer, _) = run(
                &p,
                lib.compare.unwrap(),
                &[data_address(&p, da), data_address(&p, dc)],
                bits,
            );
            let order = match a.cmp(&c) {
                std::cmp::Ordering::Less => 0u8,
                std::cmp::Ordering::Equal => 1,
                std::cmp::Ordering::Greater => 2,
            };
            assert_eq!(answer.values, [BigUint::from(order)]);
            let (answer, _) = run(&p, lib.to_word.unwrap(), &[data_address(&p, da)], bits);
            assert_eq!(answer.values, [&a & &mask]);
        }
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "generated loop beside its repeated-reuse assertions"
)]
fn word_promotion_aliases_and_long_running_heap_reuse() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 12 * word,
        };
        let (mut p, lib, _) = program(
            conf,
            Needs {
                from_word: true,
                to_word: true,
                add: true,
                ..Needs::default()
            },
        );
        let observer = p.platform("observe");
        let check = p.declare("reuse", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let zero = b.constant(WORD, 0);
            let one = b.constant(WORD, 1);
            let rounds = b.constant(WORD, 1000);
            b.loop_(&[zero], &[], |b, state| {
                let i = state[0];
                let done = b.compare(Relation::Equal, i, rounds);
                b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                let a = b.call(lib.from_word.unwrap(), args)[0];
                let alias = b.call(lib.retain, &[a])[0];
                b.call(lib.release, &[a]);
                let sum = b.call(lib.add.unwrap(), &[alias, alias])[0];
                b.call(lib.release, &[alias]);
                observe_and_release(b, &lib, observer, sum);
                let next = b.binary(Binary::Add, i, one);
                b.continue_(&[next])
            });
            b.ret(&[zero])
        });
        let input = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        let (evaluation, seen) = run(&p, check, std::slice::from_ref(&input), bits);
        assert!(!evaluation.halted);
        assert_eq!(seen.len(), 1000);
        assert!(seen.iter().all(|n| n == &(&input * BigUint::from(2u8))));
        free_heap(&evaluation.globals, word);
        // The zero promotion path is immortal and allocates nothing.
        let (evaluation, seen) = run(&p, check, &[BigUint::default()], bits);
        assert!(!evaluation.halted);
        assert_eq!(seen, vec![BigUint::default(); 1000]);
        free_heap(&evaluation.globals, word);
    }
}

#[test]
fn freed_adjacent_blocks_coalesce_for_a_larger_allocation() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 12 * word,
        };
        let (mut p, lib, _) = program(
            conf,
            Needs {
                from_word: true,
                add: true,
                ..Needs::default()
            },
        );
        let observer = p.platform("observe");
        let magnitude = BigUint::from(1u8) << (word * 8);
        let big = natural::constant(&mut p, conf, &magnitude).unwrap();
        let check = p.declare("coalesce", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let first = b.call(lib.from_word.unwrap(), args)[0];
            let second = b.call(lib.from_word.unwrap(), args)[0];
            let last = b.call(lib.from_word.unwrap(), args)[0];
            b.call(lib.release, &[first]);
            b.call(lib.release, &[second]);
            let big = b.address_of(big);
            let sum = b.call(lib.add.unwrap(), &[big, big])[0];
            observe_and_release(b, &lib, observer, sum);
            observe_and_release(b, &lib, observer, last);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero])
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(7u8)], bits);
        assert!(!evaluation.halted);
        assert_eq!(seen, [&magnitude + &magnitude, BigUint::from(7u8)]);
        free_heap(&evaluation.globals, word);
    }
}

#[test]
fn exhaustion_halts_without_corrupting_the_heap() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 4 * word,
        };
        let (mut p, lib, _) = program(
            conf,
            Needs {
                from_word: true,
                mul: true,
                ..Needs::default()
            },
        );
        let observer = p.platform("observe");
        let check = p.declare("exhaust", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let first = b.call(lib.from_word.unwrap(), args)[0];
            b.platform_call(observer, &[first]);
            let second = b.call(lib.from_word.unwrap(), args)[0];
            b.platform_call(observer, &[second]);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero])
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(1u8)], bits);
        assert!(evaluation.halted);
        assert_eq!(evaluation.values, [BigUint::from(2u8)]);
        assert_eq!(
            seen,
            [BigUint::from(1u8)],
            "effects before OOM happen exactly once"
        );
        assert_eq!(evaluation.globals.len(), 4 * word);
        assert_eq!(
            read_word(&evaluation.globals[..word]),
            u64::try_from(4 * word).unwrap()
        );
        assert_eq!(read_word(&evaluation.globals[word..2 * word]), 1);
    }
}

#[test]
fn oversized_results_halt_before_allocation() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 4 * word,
        };
        let (mut p, lib, _) = program(
            conf,
            Needs {
                mul: true,
                ..Needs::default()
            },
        );
        let huge = natural::constant(&mut p, conf, &(BigUint::from(1u8) << (word * 16))).unwrap();
        let (evaluation, _) = run(
            &p,
            lib.mul.unwrap(),
            &[data_address(&p, huge), data_address(&p, huge)],
            bits,
        );
        assert!(evaluation.halted);
        assert_eq!(evaluation.values, [BigUint::from(2u8)]);
        free_heap(&evaluation.globals, word);
    }
}

#[test]
fn reference_count_exhaustion_does_not_create_an_immortal_object() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(
            conf,
            Needs {
                from_word: true,
                ..Needs::default()
            },
        );
        let check = p.declare("count_overflow", &[], &[WORD]);
        let max = u64::MAX >> (64 - bits);
        p.define(check, |b, _| {
            let one = b.constant(WORD, 1);
            let object = b.call(lib.from_word.unwrap(), &[one])[0];
            // Test-only injection: no feasible test needs MAX-1 live aliases.
            let count = b.constant(WORD, max - 1);
            b.store(super::Width::Word, object, super::Offset::Words(1), count);
            b.call(lib.retain, &[object]);
            b.ret(&[one])
        });
        let (evaluation, _) = run(&p, check, &[], bits);
        assert!(evaluation.halted);
        assert_eq!(evaluation.values, [BigUint::from(2u8)]);
        let word = usize::from(bits / 8);
        assert_eq!(read_word(&evaluation.globals[word..2 * word]), max - 1);
    }
}

#[test]
fn immortal_and_mortal_identity_results_have_correct_claims() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(
            conf,
            Needs {
                from_word: true,
                modulo: true,
                ..Needs::default()
            },
        );
        let observer = p.platform("observe");
        let check = p.declare("identity", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let a = b.call(lib.from_word.unwrap(), args)[0];
            let zero = b.address_of(lib.zero);
            let same = b.call(lib.modulo.unwrap(), &[a, zero])[0];
            b.call(lib.release, &[a]);
            observe_and_release(b, &lib, observer, same);
            let alias = b.call(lib.retain, &[zero])[0];
            b.call(lib.release, &[zero]);
            observe_and_release(b, &lib, observer, alias);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero])
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(513u32)], bits);
        assert!(!evaluation.halted);
        assert_eq!(seen, [BigUint::from(513u32), BigUint::default()]);
        free_heap(&evaluation.globals, usize::from(bits / 8));
    }
}
