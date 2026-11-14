//! Preserve sequence order and live snapshots when fusing short prepends.

use super::{BigUint, Binary, Class, Op, Program, count, returns, settled};

#[test]
fn reversing_a_fresh_group_onto_a_sequence_writes_each_element_directly() {
    // Each case builds [1, 2, ..., n], takes a view, reverses it onto [9],
    // then reads back the result as decimal digits. A shared group also
    // contributes its original head, so that snapshot has to stay live.
    for (size, skip, len, shared, expected, fused) in [
        (1, 0, 1, false, 19u64, true),
        (4, 0, 4, false, 43_219, true),
        (5, 0, 5, false, 543_219, false),
        (3, 1, 2, false, 329, false),
        (3, 0, 2, false, 219, false),
        (2, 0, 2, true, 220, false),
    ] {
        let p = reversed_group(size, skip, len, shared);
        let held = settled(&p);
        assert_eq!(returns(&held), BigUint::from(expected));
        assert_eq!(
            count(&held, |op| matches!(op, Op::BufferPrepend { .. })),
            usize::from(!fused)
        );
        if fused {
            assert_eq!(
                count(&held, |op| matches!(op, Op::BufferPush { .. })),
                usize::try_from(size).unwrap() + 1
            );
        }
    }
}

fn reversed_group(size: u64, skip: u64, len: u64, shared: bool) -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let shape = b.shape(&[Class::Word]);
        let zero = b.constant(Class::Word, 0);
        let one = b.constant(Class::Word, 1);
        let empty = b.buffer_empty(shape);
        let nine = b.constant(Class::Word, 9);
        let [dest, start] = b.buffer_push((empty, zero, zero), shape, &[nine]);
        let (mut group, mut first) = (empty, zero);
        for digit in (1..=size).rev() {
            let used = b.constant(Class::Word, size - digit);
            let digit = b.constant(Class::Word, digit);
            [group, first] = b.buffer_push((group, first, used), shape, &[digit]);
        }
        let view = if skip == 0 {
            first
        } else {
            b.binary(Binary::Add, first, one)
        };
        let length = b.constant(Class::Word, len);
        let [out, mut at] = b.buffer_prepend((dest, start, one), (group, view, length), shape);
        let ten = b.constant(Class::Word, 10);
        let mut answer = zero;
        for _ in 0..=len {
            answer = b.binary(Binary::Mul, answer, ten);
            let digit = b.buffer_field((Class::Word, shape), (out, at), 0);
            answer = b.binary(Binary::Add, answer, digit);
            at = b.binary(Binary::Add, at, one);
        }
        if shared {
            let original = b.buffer_field((Class::Word, shape), (group, first), 0);
            answer = b.binary(Binary::Add, answer, original);
        }
        b.ret(&[answer]);
    });
    p
}
