//! The same ownership graph is interpreted here and executed by native targets.
use num_bigint::BigUint;

use super::evaluate::{self, Evaluation, Host, HostResult, Memory};
use super::test_support::{no_live_objects, word};
use super::*;
use crate::lifetime_fixture as fixture;

struct Observer {
    bytes: Vec<u8>,
    calls: Vec<String>,
}

/// A projection crosses a branch and a loop, then escapes twice. Both
/// returned aliases must survive reclamation of the original parent.
fn escaping_children(p: &mut Program, link: ShapeId) -> FunctionId {
    let select = p.declare("select", &[Class::Cell, Class::Word], &[Class::Cell; 2]);
    p.define(select, |b, args| {
        let child = b.cell_field((Class::Cell, link), args[0], 0);
        let leaf = b.cell_field((Class::Cell, link), child, 0);
        let joined = b.if_(
            args[1],
            &[Class::Cell],
            |b| b.yield_(&[leaf]),
            |b| b.ret(&[leaf, leaf]),
        );
        let one = b.constant(Class::Word, 1);
        let result = b.loop_(&[joined[0], one], &[Class::Cell], |b, state| {
            b.if_(
                state[1],
                &[],
                |b| {
                    let zero = b.constant(Class::Word, 0);
                    b.continue_(&[leaf, zero]);
                },
                |b| b.break_(&[state[0]]),
            );
        });
        b.ret(&[result[0], leaf]);
    });
    select
}

#[test]
fn projected_children_acquire_claims_when_they_escape_a_borrowed_root() {
    for choice in [0, 1] {
        let (mut p, main) = Program::new("main");
        let link = p.shape(&[Class::Cell]);
        let payload = p.shape(&[Class::Word]);
        let select = escaping_children(&mut p, link);
        p.define(main, |b, _| {
            let old = b.constant(Class::Word, 21);
            let leaf = b.cell(0, payload, &[old]);
            let inner = b.cell(0, link, &[leaf]);
            let root = b.cell(0, link, &[inner]);
            let choice = b.constant(Class::Word, choice);
            let aliases = b.call(select, &[root, choice]);
            // Reuse freed space before observing the old value.
            let new = b.constant(Class::Word, 99);
            let fresh = b.cell(0, payload, &[new]);
            let values: Vec<_> = [aliases[0], aliases[1], fresh]
                .into_iter()
                .map(|cell| b.cell_field((Class::Word, payload), cell, 0))
                .collect();
            let sum = b.binary(Binary::Add, values[0], values[1]);
            let sum = b.binary(Binary::Add, sum, values[2]);
            b.ret(&[sum]);
        });
        let config = natural::Config {
            word_bits: 64,
            heap_bytes: 512,
            grows: false,
            inline_small: true,
            inline_counts: false,
            join_routines: false,
        };
        assert_eq!(p.render().matches("# borrowed from caller").count(), 2);
        let scalar = legalize(&p, config).unwrap();
        let (after, _) = run(&scalar, 64, &[]);
        assert_eq!(after.returned().unwrap(), [BigUint::from(141u8)]);
        assert_eq!(after.outcome, run(&p, 64, &[]).0.outcome);
        no_live_objects(&scalar, &after, config);
    }
}

impl Host for Observer {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, evaluate::Error> {
        self.calls.push(name.to_owned());
        match name {
            "write!" => {
                let address = u64::try_from(word(&args[0].to_bytes_le())).unwrap();
                let len = word(&args[1].to_bytes_le());
                self.bytes.extend_from_slice(memory.read(address, len)?);
                Ok(HostResult::Return(vec![]))
            }
            "exit!" => Ok(HostResult::Halt(args.to_vec())),
            _ => Err(evaluate::Error::Host(name.to_owned())),
        }
    }
}

/// Run `p` handed the entry arguments `args`.
fn run(p: &Program, bits: u16, args: &[u64]) -> (Evaluation, Observer) {
    validate(p).expect("valid fixture");
    let mut host = Observer {
        bytes: Vec::new(),
        calls: Vec::new(),
    };
    let result = evaluate::evaluate(
        p,
        p.entry(),
        &args.iter().copied().map(BigUint::from).collect::<Vec<_>>(),
        evaluate::Config {
            word_bits: bits,
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut host,
    )
    .expect("ownership fixture execution");
    assert!(
        result.returned().is_some(),
        "unexpected runtime exhaustion: {result:?}"
    );
    (result, host)
}

#[test]
fn nested_lifetimes_preserve_full_values_and_free_every_mortal_claim() {
    // Leaking even the smallest mortal object per iteration cannot fit:
    // on the narrowest target a header and one digit occupy eight bytes.
    assert!(fixture::ITERATIONS * 8 > u64::try_from(fixture::HEAP_BYTES).unwrap());
    for bits in [16, 32, 64] {
        for early in [false, true] {
            let original = fixture::program(early);
            let config = natural::Config {
                word_bits: bits,
                heap_bytes: fixture::HEAP_BYTES,
                grows: false,
                inline_small: true,
                inline_counts: false,
                join_routines: false,
            };
            let scalar = legalize(&original, config).unwrap();
            for argc in [1, 3] {
                let (before, before_host) = run(&original, bits, &[argc]);
                let (after, after_host) = run(&scalar, bits, &[argc]);
                assert_eq!(before.returned().unwrap(), [BigUint::from(0u8)]);
                assert_eq!(after.outcome, before.outcome);
                assert_eq!(before_host.bytes, fixture::expected(argc));
                assert_eq!(
                    after_host.bytes, before_host.bytes,
                    "{bits}-bit, early={early}, argc={argc}"
                );
                assert_eq!(before_host.calls, ["write!"]);
                assert_eq!(after_host.calls, before_host.calls);
                no_live_objects(&scalar, &after, config);
            }
        }
    }
}

fn branching_function(p: &mut Program, offset: u64) -> FunctionId {
    let function = p.declare("branching", &[Class::Word], &[Class::Word]);
    p.define(function, |b, args| {
        let ancestor = b.convert(Class::Natural, args[0]);
        let selected = b.if_(
            args[0],
            &[Class::Natural],
            |b| {
                let word = b.constant(Class::Word, offset + 1);
                let local = b.convert(Class::Natural, word);
                let sum = b.binary(Binary::Add, ancestor, local);
                b.yield_(&[sum]);
            },
            |b| {
                let word = b.constant(Class::Word, offset + 3);
                let local = b.convert(Class::Natural, word);
                let sum = b.binary(Binary::Add, ancestor, local);
                b.yield_(&[sum]);
            },
        );
        let word = b.convert(Class::Word, selected[0]);
        b.ret(&[word]);
    });
    function
}

#[test]
fn one_global_mapping_preserves_sibling_and_cross_function_ownership() {
    for choice in [0, 1] {
        let (mut original, main) = Program::new("main");
        let functions: Vec<_> = (0..16)
            .map(|offset| branching_function(&mut original, offset))
            .collect();
        original.define(main, |b, _| {
            let arg = b.constant(Class::Word, choice);
            let mut sum = b.constant(Class::Word, 0);
            for &function in &functions {
                let value = b.call_one(function, &[arg]);
                sum = b.binary(Binary::Add, sum, value);
            }
            b.ret(&[sum]);
        });
        for bits in [16, 32, 64] {
            let config = natural::Config {
                word_bits: bits,
                heap_bytes: 256,
                grows: false,
                inline_small: true,
                inline_counts: false,
                join_routines: false,
            };
            let scalar = legalize(&original, config).unwrap();
            let (before, _) = run(&original, bits, &[]);
            let (after, _) = run(&scalar, bits, &[]);
            let expected = 120 + 16 * if choice == 0 { 3u64 } else { 2 };
            assert_eq!(before.returned().unwrap(), [BigUint::from(expected)]);
            assert_eq!(after.outcome, before.outcome);
            no_live_objects(&scalar, &after, config);
        }
    }
}

fn widened_loop(initial_bits: u16) -> Program {
    let (mut p, main) = Program::new("main");
    let mut parameter = None;
    p.define(main, |b, _| {
        let one = b.constant(Class::Word, 1);
        b.convert(Class::Natural, one); // Force representation rebuilding.
        let initial = b.constant(Class::fixed(initial_bits), 0);
        let limit = b.constant(Class::Word, 260);
        let answer = b.loop_(&[initial], &[Class::Word], |b, state| {
            parameter = Some(state[0]);
            let next = b.binary_at(Class::Word, Binary::Add, state[0], one);
            let done = b.compare(Relation::Equal, next, limit);
            b.if_(done, &[], |b| b.break_(&[next]), |b| b.continue_(&[next]));
        });
        b.ret(&answer);
    });
    // Builder derives parameter widths from initial values. A valid arena
    // transform can instead widen the carried slot while retaining that input.
    p.classes[parameter.unwrap()] = Class::Word;
    p
}

fn loop_body(p: &Program) -> RegionId {
    p.ops(p.function(p.entry()).body().unwrap())
        .iter()
        .find_map(|op| {
            if let Op::Loop { body, .. } = *op {
                Some(body)
            } else {
                None
            }
        })
        .expect("entry's loop")
}

#[test]
fn narrower_loop_initial_values_do_not_narrow_rebuilt_carried_parameters() {
    for initial_bits in [1, 8] {
        let original = widened_loop(initial_bits);
        validate(&original).expect("narrow initial values may feed a wider loop parameter");
        for bits in [16, 32, 64] {
            let config = natural::Config {
                word_bits: bits,
                heap_bytes: 64,
                grows: false,
                inline_small: true,
                inline_counts: false,
                join_routines: false,
            };
            let scalar = legalize(&original, config).unwrap();
            let params = scalar.values(scalar.region(loop_body(&scalar)).params);
            assert_eq!(params.len(), 1);
            assert_eq!(
                scalar.class(params[0]),
                Class::Word,
                "preserve declared loop width"
            );
            let (before, _) = run(&original, bits, &[]);
            let (after, _) = run(&scalar, bits, &[]);
            assert_eq!(before.returned().unwrap(), [BigUint::from(260u16)]);
            assert_eq!(
                after.outcome, before.outcome,
                "{initial_bits}-bit initial, {bits}-bit word"
            );
            no_live_objects(&scalar, &after, config);
        }
    }
}

#[test]
fn packed_boundaries_carry_managed_values_without_leaking_a_claim() {
    // Every function, `if` and loop in the fixture carrying two values or
    // more now carries a cell, and naturals ride in some of them.
    let budget = Budget::new(1, 1, 1);
    // A pack is an object of its own, live beside what it carries, so this
    // takes more room at once than the fixture does unpacked. It is still a
    // constant: a claim leaked per iteration would not fit.
    let heap = 2 * fixture::HEAP_BYTES;
    assert!(fixture::ITERATIONS * 8 > u64::try_from(heap).unwrap());
    for bits in [16, 32, 64] {
        for early in [false, true] {
            let fitted = fit(&fixture::program(early), budget);
            validate(&fitted).expect("a fitted program is valid");
            assert!(fitted.ops.iter().any(|op| matches!(op, Op::Cell { .. })));
            let config = natural::Config {
                word_bits: bits,
                heap_bytes: 8192,
                grows: false,
                inline_small: true,
                inline_counts: false,
                join_routines: false,
            };
            let scalar = legalize(&fitted, config).unwrap();
            for argc in [1, 3] {
                let (before, before_host) = run(&fitted, bits, &[argc]);
                let (after, after_host) = run(&scalar, bits, &[argc]);
                assert_eq!(before.returned().unwrap(), [BigUint::from(0u8)]);
                assert_eq!(after.outcome, before.outcome);
                assert_eq!(before_host.bytes, fixture::expected(argc));
                assert_eq!(after_host.bytes, before_host.bytes);
                no_live_objects(&scalar, &after, config);
            }
        }
    }
}
