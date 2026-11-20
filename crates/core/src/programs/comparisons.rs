//! Naturals that only reach comparisons, which preparation may pass as
//! words, and naturals that must stay arbitrary-precision beside them.

use crate::ir::{Binary, Class, FunctionId, Program, Relation};

/// Distinct return values make equal, unsigned-less and unsigned-greater
/// distinguishable at the machine's sign bit and at the largest word.
fn ordering(p: &mut Program) -> FunctionId {
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

/// Every call orders exact 64-bit words, so `order` (the function
/// answered) can take two words; the program answers 3.
#[must_use]
pub fn of_words() -> (Program, FunctionId) {
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
    (p, order)
}

/// One call orders a number past any word, so every call keeps the
/// natural; the program answers 5.
#[must_use]
pub fn one_past_a_word() -> Program {
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
    p
}

/// A compared parameter is also returned, so it stays natural; the
/// program answers 1.
#[must_use]
pub fn a_compared_peer_escapes() -> Program {
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
    p
}
