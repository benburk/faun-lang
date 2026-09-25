use num_bigint::BigUint;

use super::evaluate::{self, Evaluation, Host, HostResult, Memory};
use super::natural::{self, Config, Helper, Library, Needs};
use super::{Binary, Builder, Class, DataId, FunctionId, Op, Program, Relation};

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
            "exit!" => Ok(HostResult::Halt(args.to_vec())),
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

fn observer(p: &mut Program) -> FunctionId {
    p.external("observe", &[ADDRESS], super::Returns::Values(&[]))
}

fn test_program() -> (Program, FunctionId) {
    let (mut p, entry) = Program::new("test");
    p.define(entry, |b, _| {
        let zero = b.constant(WORD, 0);
        b.ret(&[zero]);
    });
    (p, entry)
}

fn program(config: Config, needs: Needs) -> (Program, Library, FunctionId) {
    let (mut p, entry) = test_program();
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
    for (size, refs) in partition(globals, word) {
        assert_eq!(refs, 0, "unreleased {size}-byte allocation");
    }
}

fn partition(globals: &[u8], word: usize) -> Vec<(usize, u64)> {
    let mut blocks = Vec::new();
    let mut cursor = 0;
    while cursor < globals.len() {
        let size = usize::try_from(read_word(&globals[cursor..cursor + word])).unwrap();
        assert!(size >= 4 * word && size.is_multiple_of(word));
        assert!(cursor + size <= globals.len());
        let refs = read_word(&globals[cursor + word..cursor + 2 * word]);
        blocks.push((size, refs));
        cursor += size;
    }
    assert_eq!(cursor, globals.len());
    blocks
}

fn data_address(p: &Program, datum: DataId) -> BigUint {
    BigUint::from(u64::from(p.datum(datum).start) + 1)
}

fn observe_and_release(
    b: &mut Builder<'_>,
    lib: &Library,
    observer: FunctionId,
    value: super::ValueId,
) {
    b.call(observer, &[value]);
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
            5,
            "entry, exit declaration, failure, retain, release only"
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
fn every_helper_subset_resolves_exactly_its_requested_handles() {
    for mask in 0u16..(1 << Helper::ALL.len()) {
        let mut needs = Needs::default();
        for (at, helper) in Helper::ALL.into_iter().enumerate() {
            if mask & (1 << at) != 0 {
                needs.insert(helper);
            }
        }
        let (p, library, _) = program(config(32), needs);
        super::validate(&p).unwrap();
        for helper in Helper::ALL {
            assert_eq!(
                library.get(helper).is_some(),
                needs.contains(helper),
                "{mask}: {helper:?}"
            );
        }
    }
}

#[test]
fn unused_arithmetic_families_are_not_generated() {
    for bits in [16, 32, 64] {
        let (p, _, _) = program(config(bits), Needs::from([Helper::Add]));
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
        let (p, _, _) = program(config(bits), Needs::from(Helper::ALL));
        super::validate(&p).unwrap();
        for f in p.functions() {
            assert!(f.params.len() <= 4);
            assert!(f.returns.classes().len() <= 1);
            let Some(body) = f.body() else { continue };
            assert!(
                region_values(&p, body) <= 128,
                "{} fits frame slots",
                p.name(f.name)
            );
            for op in p.every(body) {
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
            Needs::from([
                Helper::Add,
                Helper::Sub,
                Helper::Mul,
                Helper::Div,
                Helper::Mod,
            ]),
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
                assert!(evaluation.returned().is_some(), "{bits} {op:?} {a} {c}");
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
    let observer = observer(p);
    [
        (Binary::Add, lib.get(Helper::Add)),
        (Binary::Sub, lib.get(Helper::Sub)),
        (Binary::Mul, lib.get(Helper::Mul)),
        (Binary::Div, lib.get(Helper::Div)),
        (Binary::Mod, lib.get(Helper::Mod)),
    ]
    .into_iter()
    .map(|(op, function)| {
        let check = p.declare("check", &[ADDRESS, ADDRESS], &[WORD]);
        p.define(check, |b, args| {
            let out = b.call_one(function.unwrap(), args);
            observe_and_release(b, lib, observer, out);
            // Arithmetic borrows rather than consumes or mutates operands.
            b.call(observer, &[args[0]]);
            b.call(observer, &[args[1]]);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        (op, check)
    })
    .collect()
}

fn model(op: Binary, a: &BigUint, c: &BigUint) -> BigUint {
    match op {
        Binary::Add => a + c,
        Binary::Sub | Binary::Monus if a < c => BigUint::default(),
        Binary::Sub | Binary::Monus => a - c,
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
        let (mut p, lib, _) = program(conf, Needs::from([Helper::Compare, Helper::ToWord]));
        assert!(p.globals().is_empty());
        let mask = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        for (a, c) in samples(bits) {
            let da = natural::constant(&mut p, conf, &a).unwrap();
            let dc = natural::constant(&mut p, conf, &c).unwrap();
            let (answer, _) = run(
                &p,
                lib.require(Helper::Compare),
                &[data_address(&p, da), data_address(&p, dc)],
                bits,
            );
            let order = match a.cmp(&c) {
                std::cmp::Ordering::Less => 0u8,
                std::cmp::Ordering::Equal => 1,
                std::cmp::Ordering::Greater => 2,
            };
            assert_eq!(answer.returned().unwrap(), [BigUint::from(order)]);
            let (answer, _) = run(
                &p,
                lib.require(Helper::ToWord),
                &[data_address(&p, da)],
                bits,
            );
            assert_eq!(answer.returned().unwrap(), [&a & &mask]);
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
            Needs::from([Helper::FromWord, Helper::ToWord, Helper::Add]),
        );
        let observer = observer(&mut p);
        let check = p.declare("reuse", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let zero = b.constant(WORD, 0);
            let one = b.constant(WORD, 1);
            let rounds = b.constant(WORD, 1000);
            b.loop_(&[zero], &[], |b, state| {
                let i = state[0];
                let done = b.compare(Relation::Equal, i, rounds);
                b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                let a = b.call_one(lib.require(Helper::FromWord), args);
                let alias = b.call_one(lib.retain, &[a]);
                b.call(lib.release, &[a]);
                let sum = b.call_one(lib.require(Helper::Add), &[alias, alias]);
                b.call(lib.release, &[alias]);
                observe_and_release(b, &lib, observer, sum);
                let next = b.binary(Binary::Add, i, one);
                b.continue_(&[next]);
            });
            b.ret(&[zero]);
        });
        let input = (BigUint::from(1u8) << usize::from(bits)) - BigUint::from(1u8);
        let (evaluation, seen) = run(&p, check, std::slice::from_ref(&input), bits);
        assert!(evaluation.returned().is_some());
        assert_eq!(seen.len(), 1000);
        assert!(seen.iter().all(|n| n == &(&input * BigUint::from(2u8))));
        free_heap(&evaluation.globals, word);
        // The zero promotion path is immortal and allocates nothing.
        let (evaluation, seen) = run(&p, check, &[BigUint::default()], bits);
        assert!(evaluation.returned().is_some());
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
        let (mut p, lib, _) = program(conf, Needs::from([Helper::FromWord, Helper::Add]));
        let observer = observer(&mut p);
        let magnitude = BigUint::from(1u8) << (word * 8);
        let big = natural::constant(&mut p, conf, &magnitude).unwrap();
        let check = p.declare("coalesce", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let first = b.call_one(lib.require(Helper::FromWord), args);
            let second = b.call_one(lib.require(Helper::FromWord), args);
            let last = b.call_one(lib.require(Helper::FromWord), args);
            b.call(lib.release, &[first]);
            b.call(lib.release, &[second]);
            let big = b.address_of(big);
            let sum = b.call_one(lib.require(Helper::Add), &[big, big]);
            observe_and_release(b, &lib, observer, sum);
            observe_and_release(b, &lib, observer, last);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(7u8)], bits);
        assert!(evaluation.returned().is_some());
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
        let (mut p, lib, _) = program(conf, Needs::from([Helper::FromWord, Helper::Mul]));
        let observer = observer(&mut p);
        let check = p.declare("exhaust", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let first = b.call_one(lib.require(Helper::FromWord), args);
            b.call(observer, &[first]);
            let second = b.call_one(lib.require(Helper::FromWord), args);
            b.call(observer, &[second]);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(1u8)], bits);
        assert_eq!(evaluation.halted().unwrap(), [BigUint::from(2u8)]);
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
        let (mut p, lib, _) = program(conf, Needs::from([Helper::Mul]));
        let huge = natural::constant(&mut p, conf, &(BigUint::from(1u8) << (word * 16))).unwrap();
        let (evaluation, _) = run(
            &p,
            lib.require(Helper::Mul),
            &[data_address(&p, huge), data_address(&p, huge)],
            bits,
        );
        assert_eq!(evaluation.halted().unwrap(), [BigUint::from(2u8)]);
        free_heap(&evaluation.globals, word);
    }
}

#[test]
fn reference_count_exhaustion_does_not_create_an_immortal_object() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(conf, Needs::from([Helper::FromWord]));
        let check = p.declare("count_overflow", &[], &[WORD]);
        let max = u64::MAX >> (64 - bits);
        p.define(check, |b, _| {
            let one = b.constant(WORD, 1);
            let object = b.call_one(lib.require(Helper::FromWord), &[one]);
            // Test-only injection: no feasible test needs MAX-1 live aliases.
            let count = b.constant(WORD, max - 1);
            b.store(super::Width::Word, object, super::Offset::Words(1), count);
            b.call(lib.retain, &[object]);
            b.ret(&[one]);
        });
        let (evaluation, _) = run(&p, check, &[], bits);
        assert_eq!(evaluation.halted().unwrap(), [BigUint::from(2u8)]);
        let word = usize::from(bits / 8);
        assert_eq!(read_word(&evaluation.globals[word..2 * word]), max - 1);
    }
}

fn repeat(b: &mut Builder<'_>, times: u64, body: impl FnOnce(&mut Builder<'_>)) {
    let zero = b.constant(WORD, 0);
    let one = b.constant(WORD, 1);
    let times = b.constant(WORD, times);
    b.loop_(&[zero], &[], |b, state| {
        let done = b.compare(Relation::Equal, state[0], times);
        b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
        body(b);
        let next = b.binary(Binary::Add, state[0], one);
        b.continue_(&[next]);
    });
}

fn promote(b: &mut Builder<'_>, lib: &Library, value: u64) -> super::ValueId {
    let value = b.constant(WORD, value);
    b.call_one(lib.require(Helper::FromWord), &[value])
}

fn observed_product(
    b: &mut Builder<'_>,
    lib: &Library,
    observer: FunctionId,
    left: DataId,
    right: DataId,
) {
    let left = b.address_of(left);
    let right = b.address_of(right);
    let result = b.call_one(lib.require(Helper::Mul), &[left, right]);
    observe_and_release(b, lib, observer, result);
}

#[test]
fn multiplication_clears_dirty_recycled_accumulators() {
    for bits in [16, 32, 64] {
        let conf = Config {
            word_bits: bits,
            heap_bytes: 64,
        };
        let (mut p, lib, entry) = program(conf, Needs::from([Helper::Mul]));
        let observer = observer(&mut p);
        let dense = (BigUint::from(1u8) << 128usize) - BigUint::from(1u8);
        let sparse = BigUint::from(1u8) << 120usize;
        let dense_id = natural::constant(&mut p, conf, &dense).unwrap();
        let sparse_id = natural::constant(&mut p, conf, &sparse).unwrap();
        let one = natural::constant(&mut p, conf, &BigUint::from(1u8)).unwrap();
        p.define(entry, |b, _| {
            repeat(b, 100, |b| {
                observed_product(b, &lib, observer, dense_id, dense_id);
                observed_product(b, &lib, observer, sparse_id, one);
            });
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, entry, &[], bits);
        assert!(evaluation.returned().is_some());
        assert_eq!(seen.len(), 200);
        for pair in seen.chunks_exact(2) {
            assert_eq!(pair, [&dense * &dense, sparse.clone()]);
        }
        free_heap(&evaluation.globals, usize::from(bits / 8));
    }
}

#[test]
fn smaller_mortal_remainder_survives_releasing_inputs_and_reallocation() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 8 * word,
        };
        let (mut p, lib, entry) = program(conf, Needs::from([Helper::FromWord, Helper::Mod]));
        let observer = observer(&mut p);
        p.define(entry, |b, _| {
            let left = promote(b, &lib, 513);
            let right = promote(b, &lib, 514);
            let result = b.call_one(lib.require(Helper::Mod), &[left, right]);
            b.call(lib.release, &[left]);
            b.call(lib.release, &[right]);
            let replacement = promote(b, &lib, 9);
            observe_and_release(b, &lib, observer, result);
            observe_and_release(b, &lib, observer, replacement);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, entry, &[], bits);
        assert!(evaluation.returned().is_some());
        assert_eq!(seen, [BigUint::from(513u32), BigUint::from(9u8)]);
        free_heap(&evaluation.globals, word);
    }
}

fn fragmented_check(p: &mut Program, lib: &Library, big: DataId, remove_middle: bool) {
    let observer = observer(p);
    p.define(p.entry(), |b, _| {
        let first = promote(b, lib, 1);
        let middle = promote(b, lib, 2);
        let third = promote(b, lib, 3);
        let last = promote(b, lib, 4);
        b.call(lib.release, &[first]);
        b.call(lib.release, &[third]);
        if remove_middle {
            b.call(lib.release, &[middle]);
        }
        let big = b.address_of(big);
        let result = b.call_one(lib.require(Helper::Add), &[big, big]);
        // Keep the 5W result alive: this request must take the 7W remainder.
        let replacement = promote(b, lib, 9);
        observe_and_release(b, lib, observer, result);
        observe_and_release(b, lib, observer, replacement);
        observe_and_release(b, lib, observer, last);
        if !remove_middle {
            b.call(lib.release, &[middle]);
        }
        let zero = b.constant(WORD, 0);
        b.ret(&[zero]);
    });
}

#[test]
fn coalescing_stops_at_live_blocks_and_later_reuses_the_joined_run() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 16 * word,
        };
        let magnitude = BigUint::from(1u8) << usize::from(bits);
        for remove_middle in [false, true] {
            let (mut p, lib, entry) = program(conf, Needs::from([Helper::FromWord, Helper::Add]));
            let big = natural::constant(&mut p, conf, &magnitude).unwrap();
            fragmented_check(&mut p, &lib, big, remove_middle);
            let (evaluation, seen) = run(&p, entry, &[], bits);
            let blocks = partition(&evaluation.globals, word);
            if remove_middle {
                assert!(evaluation.returned().is_some());
                assert_eq!(
                    seen,
                    [
                        &magnitude + &magnitude,
                        BigUint::from(9u8),
                        BigUint::from(4u8)
                    ]
                );
                assert_eq!(blocks, [(5 * word, 0), (7 * word, 0), (4 * word, 0)]);
                free_heap(&evaluation.globals, word);
            } else {
                assert_eq!(evaluation.halted().unwrap(), [BigUint::from(2u8)]);
                assert!(seen.is_empty());
                still_fragmented(&evaluation.globals, word);
            }
        }
    }
}

fn still_fragmented(globals: &[u8], word: usize) {
    assert_eq!(
        partition(globals, word),
        [(4 * word, 0), (4 * word, 1), (4 * word, 0), (4 * word, 1)]
    );
    // The failed allocation did not modify either surviving full magnitude.
    for (offset, value) in [(4 * word, 2u8), (12 * word, 4u8)] {
        let len =
            usize::try_from(read_word(&globals[offset + 2 * word..offset + 3 * word])).unwrap();
        assert_eq!(len, 1);
        let start = offset + 3 * word;
        assert_eq!(
            BigUint::from_bytes_le(&globals[start..start + len]),
            BigUint::from(value)
        );
    }
}

fn sentinel_pair(b: &mut Builder<'_>, first: DataId, last: DataId) -> super::ValueId {
    let first = b.address_of(first);
    let last = b.address_of(last);
    let first = b.load(super::Width::Byte, first, super::Offset::Bytes(0));
    let last = b.load(super::Width::Byte, last, super::Offset::Bytes(0));
    let radix = b.constant(WORD, 256);
    let high = b.binary(Binary::Mul, first, radix);
    b.binary(Binary::Add, high, last)
}

#[test]
fn preexisting_and_unaligned_pools_keep_their_sentinels() {
    for bits in [16, 32, 64] {
        let word = usize::from(bits / 8);
        let conf = Config {
            word_bits: bits,
            heap_bytes: 128,
        };
        let (mut p, entry) = test_program();
        let sentinel = p.intern(&[0xa5]);
        p.global(&[0x5a]);
        let lib =
            natural::append(&mut p, conf, Needs::from([Helper::FromWord, Helper::Mul])).unwrap();
        let tail = p.intern(&[0x6b]); // makes the interpreter's Globals base unaligned
        assert_ne!((p.data().len() + 2 + word) % word, 0);
        let prefix = p.globals()[..word].to_vec();
        let observer = observer(&mut p);
        p.define(entry, |b, _| {
            repeat(b, 100, |b| {
                let input = promote(b, &lib, 513);
                let result = b.call_one(lib.require(Helper::Mul), &[input, input]);
                b.call(lib.release, &[input]);
                observe_and_release(b, &lib, observer, result);
            });
            let pair = sentinel_pair(b, sentinel, tail);
            b.ret(&[pair]);
        });
        let (evaluation, seen) = run(&p, entry, &[], bits);
        assert_eq!(evaluation.returned().unwrap(), [BigUint::from(0xa56bu32)]);
        assert_eq!(seen, vec![BigUint::from(513u32 * 513); 100]);
        assert_eq!(&evaluation.globals[..word], prefix);
        free_heap(&evaluation.globals[word..], word);
    }
}

#[test]
fn carry_and_borrow_cross_entire_zero_byte_runs() {
    for bits in [16, 32, 64] {
        let conf = Config {
            word_bits: bits,
            heap_bytes: 128,
        };
        let (mut p, lib, entry) = program(conf, Needs::from([Helper::Add, Helper::Sub]));
        let observer = observer(&mut p);
        let power = BigUint::from(1u8) << 128usize;
        let dense = &power - BigUint::from(1u8);
        let dense_id = natural::constant(&mut p, conf, &dense).unwrap();
        let one = natural::constant(&mut p, conf, &BigUint::from(1u8)).unwrap();
        p.define(entry, |b, _| {
            repeat(b, 32, |b| {
                let dense = b.address_of(dense_id);
                let one = b.address_of(one);
                let sum = b.call_one(lib.require(Helper::Add), &[dense, one]);
                b.call(observer, &[sum]);
                let difference = b.call_one(lib.require(Helper::Sub), &[sum, one]);
                b.call(lib.release, &[sum]);
                observe_and_release(b, &lib, observer, difference);
            });
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, entry, &[], bits);
        assert!(evaluation.returned().is_some());
        assert_eq!(seen.len(), 64);
        for pair in seen.chunks_exact(2) {
            assert_eq!(pair, [power.clone(), dense.clone()]);
        }
        free_heap(&evaluation.globals, usize::from(bits / 8));
    }
}

fn division_boundaries() -> Vec<(BigUint, BigUint, BigUint, BigUint)> {
    let n = BigUint::from;
    let high = n(1u64) << 128usize;
    let middle = n(1u64) << 64usize;
    vec![
        (n(0xffff), n(0xff), n(0x101), n(0)),
        (n(0x10000), n(0xff), n(0x101), n(1)),
        (n(0x10000), n(0x100), n(0x100), n(0)),
        (n(0x10000), n(0x101), n(0xff), n(1)),
        (high.clone(), n(257), (&high - n(1)) / n(257), n(1)),
        (&high + &middle + n(1), &middle + n(1), middle.clone(), n(1)),
        (&high - n(1), middle.clone(), &middle - n(1), &middle - n(1)),
    ]
}

#[test]
fn quotient_and_remainder_normalize_after_dirty_scratch_recycling() {
    for bits in [16, 32, 64] {
        let conf = Config {
            word_bits: bits,
            heap_bytes: 128,
        };
        let (mut p, lib, _) = program(conf, Needs::from([Helper::Mul, Helper::Div, Helper::Mod]));
        let dense = (BigUint::from(1u8) << 128usize) - BigUint::from(1u8);
        let dirty = natural::constant(&mut p, conf, &dense).unwrap();
        let observer = observer(&mut p);
        let check = p.declare("recycled_division", &[ADDRESS, ADDRESS], &[WORD]);
        p.define(check, |b, args| {
            observed_product(b, &lib, observer, dirty, dirty);
            for function in [lib.require(Helper::Div), lib.require(Helper::Mod)] {
                let value = b.call_one(function, args);
                observe_and_release(b, &lib, observer, value);
            }
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        for (a, b, quotient, remainder) in division_boundaries() {
            assert_eq!(&quotient * &b + &remainder, a);
            assert!(remainder < b);
            let left = natural::constant(&mut p, conf, &a).unwrap();
            let right = natural::constant(&mut p, conf, &b).unwrap();
            let args = [data_address(&p, left), data_address(&p, right)];
            let (evaluation, seen) = run(&p, check, &args, bits);
            assert!(evaluation.returned().is_some());
            assert_eq!(seen, [&dense * &dense, quotient, remainder]);
            free_heap(&evaluation.globals, usize::from(bits / 8));
        }
    }
}

fn isolated_needs(op: Option<Binary>) -> Needs {
    Needs::from([op.map_or(Helper::FromWord, Helper::arithmetic)])
}

fn isolated_family(bits: u16, op: Option<Binary>) {
    let conf = Config {
        word_bits: bits,
        heap_bytes: 128,
    };
    let (mut p, lib, entry) = program(conf, isolated_needs(op));
    let optional = Helper::ALL.map(|helper| lib.get(helper));
    assert_eq!(optional.iter().filter(|id| id.is_some()).count(), 1);
    let function = optional.into_iter().flatten().next().unwrap();
    let left = (BigUint::from(1u8) << 128usize) + BigUint::from(257u32);
    let right = BigUint::from(257u32);
    let left_id = natural::constant(&mut p, conf, &left).unwrap();
    let right_id = natural::constant(&mut p, conf, &right).unwrap();
    let observer = observer(&mut p);
    p.define(entry, |b, _| {
        let value = if op.is_some() {
            let left = b.address_of(left_id);
            let right = b.address_of(right_id);
            b.call_one(function, &[left, right])
        } else {
            promote(b, &lib, 513)
        };
        observe_and_release(b, &lib, observer, value);
        let zero = b.constant(WORD, 0);
        b.ret(&[zero]);
    });
    let (evaluation, seen) = run(&p, entry, &[], bits);
    assert!(evaluation.returned().is_some());
    let expected = op.map_or_else(|| BigUint::from(513u32), |op| model(op, &left, &right));
    assert_eq!(seen, [expected]);
    free_heap(&evaluation.globals, usize::from(bits / 8));
}

#[test]
fn isolated_sub_div_mod_mul_and_promotion_include_all_dependencies() {
    for bits in [16, 32, 64] {
        for op in [
            Some(Binary::Sub),
            Some(Binary::Div),
            Some(Binary::Mod),
            Some(Binary::Mul),
            None,
        ] {
            isolated_family(bits, op);
        }
    }
}

#[test]
fn retain_and_release_reject_zero_counts_without_resurrecting_storage() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        for retaining in [false, true] {
            let (mut p, lib, entry) = program(conf, Needs::from([Helper::FromWord]));
            p.define(entry, |b, _| {
                let object = promote(b, &lib, 1);
                let zero = b.constant(WORD, 0);
                b.store(super::Width::Word, object, super::Offset::Words(1), zero);
                let function = if retaining { lib.retain } else { lib.release };
                b.call(function, &[object]);
                b.ret(&[zero]);
            });
            let (evaluation, seen) = run(&p, entry, &[], bits);
            assert_eq!(evaluation.halted().unwrap(), [BigUint::from(2u8)]);
            assert!(seen.is_empty());
            free_heap(&evaluation.globals, usize::from(bits / 8));
        }
    }
}

#[test]
fn immortal_and_mortal_identity_results_have_correct_claims() {
    for bits in [16, 32, 64] {
        let conf = config(bits);
        let (mut p, lib, _) = program(conf, Needs::from([Helper::FromWord, Helper::Mod]));
        let observer = observer(&mut p);
        let check = p.declare("identity", &[WORD], &[WORD]);
        p.define(check, |b, args| {
            let a = b.call_one(lib.require(Helper::FromWord), args);
            let zero = b.address_of(lib.zero);
            let same = b.call_one(lib.require(Helper::Mod), &[a, zero]);
            b.call(lib.release, &[a]);
            observe_and_release(b, &lib, observer, same);
            let alias = b.call_one(lib.retain, &[zero]);
            b.call(lib.release, &[zero]);
            observe_and_release(b, &lib, observer, alias);
            let zero = b.constant(WORD, 0);
            b.ret(&[zero]);
        });
        let (evaluation, seen) = run(&p, check, &[BigUint::from(513u32)], bits);
        assert!(evaluation.returned().is_some());
        assert_eq!(seen, [BigUint::from(513u32), BigUint::default()]);
        free_heap(&evaluation.globals, usize::from(bits / 8));
    }
}
