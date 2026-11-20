use faun_core::ir::{Binary, Class, Offset, Program, Relation, Width};
use faun_core::programs::abi::{self, Transfer};

// The shared runner validates raw emission, without pruning results or fitting
// the ABI first. It serializes native process creation within the test binary.
use super::shared::status as execute;

#[test]
fn stack_arguments_and_results_preserve_every_value() {
    for params in [0, 1, 6, 7, 12, 32] {
        for returns in [0, 1, 2, 3, 10, 32] {
            assert_eq!(
                execute(&abi::function(params, returns)),
                0,
                "{params} -> {returns}"
            );
        }
    }
}

#[test]
fn stack_results_preserve_distinct_pointers() {
    let (mut program, main) = Program::new("main");
    let left = program.intern(&[19]);
    let right = program.intern(&[42]);
    let pair = program.declare("pair", &[], &[Class::Address; 2]);
    program.define(pair, |b, _| {
        let left = b.address_of(left);
        let right = b.address_of(right);
        b.ret(&[left, right]);
    });
    program.define(main, |b, _| {
        let pointers = b.call(pair, &[]);
        let left = b.load(Width::Byte, pointers[0], Offset::Bytes(0));
        let right = b.load(Width::Byte, pointers[1], Offset::Bytes(0));
        let sum = b.binary(Binary::Add, left, right);
        b.ret(&[sum]);
    });
    assert_eq!(execute(&program), 61);
}

/// Every recursive activation has outgoing arguments/results, incoming
/// arguments/results, spills and saved registers live at the same time.
#[test]
fn recursion_keeps_incoming_outgoing_and_spilled_values_separate() {
    let (mut program, main) = Program::new("main");
    let recurse = program.declare("recurse", &[Class::Word; 16], &[Class::Word; 15]);
    program.define(recurse, |b, args| {
        let zero = b.constant(Class::Word, 0);
        let done = b.compare(Relation::Equal, args[0], zero);
        b.if_(
            done,
            &[],
            |b| b.ret(&args[1..]),
            |b| {
                let one = b.constant(Class::Word, 1);
                let depth = b.binary(Binary::Sub, args[0], one);
                let mut next = vec![depth];
                next.extend(args[1..].iter().rev());
                let returned = b.call(recurse, &next);
                let answer: Vec<_> = returned
                    .iter()
                    .zip(&args[1..])
                    .map(|(&returned, &original)| b.binary(Binary::Add, returned, original))
                    .collect();
                b.ret(&answer);
            },
        );
    });
    program.define(main, |b, _| {
        let mut args = vec![b.constant(Class::Word, 4)];
        args.extend((1..=15).map(|n| b.constant(Class::Word, n)));
        let returned = b.call(recurse, &args);
        // Four reversals/additions produce 3*x + 2*(16-x) = 32+x.
        let mut passed = b.constant(Class::Word, 0);
        for (value, expected) in returned.into_iter().zip(33..=47) {
            let expected = b.constant(Class::Word, expected);
            let equal = b.compare(Relation::Equal, value, expected);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(Class::Word, 15);
        let failed = b.binary(Binary::Sub, count, passed);
        b.ret(&[failed]);
    });
    assert_eq!(execute(&program), 0);
}

#[test]
fn repeated_stack_arguments_and_results_and_reused_call_areas() {
    let (mut program, main) = Program::new("main");
    let wide = program.declare("wide", &[Class::Word; 20], &[Class::Word; 12]);
    program.define(wide, |b, args| b.ret(&[args[19]; 12]));
    let small = program.declare("small", &[Class::Word; 7], &[Class::Word; 2]);
    program.define(small, |b, args| b.ret(&[args[6], args[0]]));
    program.define(main, |b, _| {
        let seven = b.constant(Class::Word, 7);
        let first = b.call(wide, &[seven; 20]);
        let second = b.call(small, &[first[11]; 7]);
        let third = b.call(wide, &[second[1]; 20]);
        let sum = b.binary(Binary::Add, first[0], third[11]);
        b.ret(&[sum]);
    });
    assert_eq!(execute(&program), 14);
}

#[test]
fn accepts_multivalue_regions() {
    for kind in [Transfer::If, Transfer::LoopState, Transfer::LoopResults] {
        assert_eq!(execute(&abi::region(kind, 3)), 0);
    }
}
