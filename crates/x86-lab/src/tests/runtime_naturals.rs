use super::faun;
use crate as faun_core;

include!("../../../core/tests/support/runtime_naturals.rs");

#[test]
fn source_runtime_naturals_can_be_compared_before_a_bounded_host_effect() {
    source_check(&crate::X86_64Linux, None);
}

/// Raw acceptance still enforces the native convention; the compilation
/// wrappers fit a program to it first, managed results included.
#[test]
fn compilation_wrappers_fit_programs_to_native_abi_limits() {
    use crate::programs::abi;
    let (mut pair_of_naturals, main) = Program::new("main");
    pair_of_naturals.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let pair =
        pair_of_naturals.declare("pair", &[Class::Natural], &[Class::Natural, Class::Natural]);
    pair_of_naturals.define(pair, |b, args| b.ret(&[args[0], args[0]]));
    let target = crate::X86_64Linux;
    for p in [
        pair_of_naturals,
        abi::function(6, 1),
        abi::function(7, 1),
        abi::function(0, 2),
        abi::pointer_pair(),
        abi::region(abi::Transfer::LoopState, 3),
    ] {
        let prepared = target.prepare(&p).unwrap();
        target.accepts(&prepared).unwrap();
        target.compile_machine_ir(&p).unwrap();
    }
}

#[test]
fn runtime_naturals_write_all_result_bytes() {
    check(&crate::X86_64Linux, None);
}

/// Distinct return values make equal, unsigned-less and unsigned-greater
/// distinguishable at the machine's sign bit and at the largest word.
fn ordering(p: &mut Program) -> crate::ir::FunctionId {
    use crate::ir::Relation;
    let order = p.declare("order", &[Class::Natural; 2], &[Class::Word]);
    p.define(order, |b, args| {
        let less = b.compare(Relation::Less, args[0], args[1]);
        b.if_(
            less,
            &[],
            |b| {
                let one = b.constant(Class::Word, 1);
                b.ret(&[one]);
            },
            |b| {
                let equal = b.compare(Relation::Equal, args[0], args[1]);
                let two = b.constant(Class::Word, 2);
                let result = b.binary(Binary::Add, equal, two);
                b.ret(&[result]);
            },
        );
    });
    order
}

#[test]
fn comparison_only_parameters_use_unsigned_words_across_branches() {
    use crate::ir::{Relation, word_comparisons};
    let (mut p, main) = Program::new("main");
    let order = ordering(&mut p);
    p.define(main, |b, _| {
        let mut passes = b.constant(Class::Word, 0);
        for (a, c, expected) in [
            (0, u64::MAX, 1),
            (1 << 63, (1 << 63) - 1, 2),
            (u64::MAX, u64::MAX, 3),
        ] {
            let word = b.constant(Class::fixed(64), a);
            let a = b.convert(Class::Natural, word);
            let c = b.constant(Class::Natural, c);
            let got = b.call_one(order, &[a, c]);
            let expected = b.constant(Class::Word, expected);
            let pass = b.compare(Relation::Equal, got, expected);
            passes = b.binary(Binary::Add, passes, pass);
        }
        b.ret(&[passes]);
    });
    let lowered = word_comparisons::lower(&p, 64).unwrap();
    assert_eq!(
        lowered.signature(lowered.function(order).params),
        [Class::Word; 2]
    );
    assert!(
        !lowered
            .every(lowered.function(main).body().unwrap())
            .any(|op| matches!(op, crate::ir::Op::Convert { .. }))
    );
    assert!(word_comparisons::lower(&p, 32).is_none());
    assert_eq!(
        super::shared::status(&super::TARGET.prepare(&p).unwrap()),
        3
    );
}

#[test]
fn one_arbitrary_precision_call_preserves_the_comparison_for_every_caller() {
    use crate::ir::word_comparisons;
    let (mut p, main) = Program::new("main");
    let order = ordering(&mut p);
    p.define(main, |b, _| {
        let small = b.constant(Class::Natural, 42);
        let first = b.call_one(order, &[small, small]);
        let big = b.natural(&(num_bigint::BigUint::from(1u8) << 96usize));
        let second = b.call_one(order, &[big, small]);
        let result = b.binary(Binary::Add, first, second);
        b.ret(&[result]);
    });
    assert!(word_comparisons::lower(&p, 64).is_none());
    assert_eq!(
        super::shared::status(&super::TARGET.prepare(&p).unwrap()),
        5
    );
}

#[test]
fn comparison_parameters_stay_natural_when_their_peer_escapes() {
    use crate::ir::{Relation, word_comparisons};
    let (mut p, main) = Program::new("main");
    let select = p.declare("select", &[Class::Natural; 2], &[Class::Natural]);
    p.define(select, |b, args| {
        let less = b.compare(Relation::Less, args[0], args[1]);
        b.if_(
            less,
            &[],
            |b| {
                let one = b.constant(Class::Natural, 1);
                b.ret(&[one]);
            },
            |b| b.ret(&[args[0]]),
        );
    });
    p.define(main, |b, _| {
        let large = b.constant(Class::Natural, u64::MAX);
        let small = b.constant(Class::Natural, 42);
        let result = b.call_one(select, &[large, small]);
        let got = b.compare(Relation::Equal, result, large);
        b.ret(&[got]);
    });
    assert!(word_comparisons::lower(&p, 64).is_none());
    assert_eq!(
        super::shared::status(&super::TARGET.prepare(&p).unwrap()),
        1
    );
}
