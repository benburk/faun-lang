//! The same ownership graph is interpreted here and executed by native targets.
use num_bigint::BigUint;

use super::evaluate::{self, Evaluation, Host, HostResult, Memory};
use super::test_support::{no_live_objects, word};
use super::*;
use crate::{ir, targets};

#[path = "../../tests/support/runtime_lifetimes.rs"]
#[expect(
    dead_code,
    reason = "the native runner is used by target integration tests"
)]
mod fixture;

struct Observer {
    argc: u64,
    bytes: Vec<u8>,
    calls: Vec<String>,
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
            "argc" => Ok(HostResult::Return(vec![BigUint::from(self.argc)])),
            "write" => {
                let address = u64::try_from(word(&args[0].to_bytes_le())).unwrap();
                let len = word(&args[1].to_bytes_le());
                self.bytes.extend_from_slice(memory.read(address, len)?);
                Ok(HostResult::Return(vec![]))
            }
            "exit" => Ok(HostResult::Halt(args.to_vec())),
            _ => Err(evaluate::Error::Host(name.to_owned())),
        }
    }
}

fn run(p: &Program, bits: u16, argc: u64) -> (Evaluation, Observer) {
    validate(p).expect("valid fixture");
    let mut host = Observer {
        argc,
        bytes: Vec::new(),
        calls: Vec::new(),
    };
    let result = evaluate::evaluate(
        p,
        p.entry(),
        &[],
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
            };
            let scalar = legalize(&original, config).unwrap();
            for argc in [1, 3] {
                let (before, before_host) = run(&original, bits, argc);
                let (after, after_host) = run(&scalar, bits, argc);
                assert_eq!(before.returned().unwrap(), [BigUint::from(0u8)]);
                assert_eq!(after.outcome, before.outcome);
                assert_eq!(before_host.bytes, fixture::expected(argc));
                assert_eq!(
                    after_host.bytes, before_host.bytes,
                    "{bits}-bit, early={early}, argc={argc}"
                );
                assert_eq!(before_host.calls, ["argc", "write"]);
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
            };
            let scalar = legalize(&original, config).unwrap();
            let (before, _) = run(&original, bits, 0);
            let (after, _) = run(&scalar, bits, 0);
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
        let initial = b.constant(Class::Fixed { bits: initial_bits }, 0);
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
            };
            let scalar = legalize(&original, config).unwrap();
            let params = scalar.values(scalar.region(loop_body(&scalar)).params);
            assert_eq!(params.len(), 1);
            assert_eq!(
                scalar.class(params[0]),
                Class::Word,
                "preserve declared loop width"
            );
            let (before, _) = run(&original, bits, 0);
            let (after, _) = run(&scalar, bits, 0);
            assert_eq!(before.returned().unwrap(), [BigUint::from(260u16)]);
            assert_eq!(
                after.outcome, before.outcome,
                "{initial_bits}-bit initial, {bits}-bit word"
            );
            no_live_objects(&scalar, &after, config);
        }
    }
}
