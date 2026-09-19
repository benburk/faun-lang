//! Shared executable arithmetic checks.
//!
//! Calls take runtime parameters, not folded Barb constants. Each program returns zero only if every full-width
//! answer agrees, so checking an eight-bit process status loses no coverage.

use crate::ir::{Binary, Class, Program, Relation};

/// Boundary checks at a target-supported width. No multiplication here
/// overflows its declared class; division includes the unsigned high bit.
#[must_use]
pub fn boundaries(bits: u16, op: Binary) -> Program {
    if bits == 0 {
        return cases(bits, op, &[(0, 0)]);
    }
    let max = u64::MAX >> (64 - bits);
    let high = 1u64 << (bits - 1);
    let mut pairs = if op == Binary::Mul {
        vec![
            (0, max),
            (max, 0),
            (1, max),
            (max, 1),
            (max / 3, 3),
            (high / 2, 2),
        ]
    } else {
        vec![
            (0, 0),
            (max, 0),
            (max, 1),
            (max, max),
            (max, high),
            (high, max),
            (max, 3),
            (1, max),
        ]
    };
    pairs.retain(|&(left, right)| left <= max && right <= max);
    cases(bits, op, &pairs)
}

/// Execute a collection of valid inputs through one arithmetic function.
///
/// The expected value is the third parameter (RDX under System V), and
/// remains live across the multiply/divide's implicit register clobber.
///
/// # Panics
/// If an input overflows u64 arithmetic or subtraction is not guarded.
#[must_use]
pub fn cases(bits: u16, op: Binary, pairs: &[(u64, u64)]) -> Program {
    let class = Class::Fixed { bits };
    let (mut program, main) = Program::new("main");
    let check = program.declare("check", &[class, class, class], &[Class::Word]);
    program.define(check, |b, args| {
        let actual = b.binary(op, args[0], args[1]);
        let equal = b.compare(Relation::Equal, actual, args[2]);
        b.ret(&[equal]);
    });
    program.define(main, |b, _| {
        let mut passed = b.constant(Class::Word, 0);
        for &(left, right) in pairs {
            let expected = match op {
                Binary::Mul => left.checked_mul(right).expect("a fitting product"),
                Binary::Div => left.checked_div(right).unwrap_or(0),
                Binary::Mod => left.checked_rem(right).unwrap_or(left),
                Binary::Add => left.checked_add(right).expect("a fitting sum"),
                Binary::Sub => left.checked_sub(right).expect("a guarded subtraction"),
            };
            let args = [left, right, expected].map(|value| b.constant(class, value));
            let result = b.call_one(check, &args);
            passed = b.binary(Binary::Add, passed, result);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(pairs.len()).expect("a few cases"),
        );
        let failures = b.binary(Binary::Sub, count, passed);
        b.ret(&[failures]);
    });
    program
}

/// An odd-width explicit truncation, followed by a product that needs a
/// wider class. Promotion must not truncate to the operand's old width.
#[must_use]
pub fn odd_conversion() -> Program {
    let small = Class::Fixed { bits: 7 };
    let wide = Class::Fixed { bits: 15 };
    let (mut program, main) = Program::new("main");
    let check = program.declare("convert", &[wide], &[Class::Word]);
    program.define(check, |b, args| {
        let low = b.convert(small, args[0]);
        let square = b.binary_at(wide, Binary::Mul, low, low);
        let expected = b.constant(wide, 127 * 127);
        let equal = b.compare(Relation::Equal, square, expected);
        let one = b.constant(Class::Word, 1);
        let failure = b.binary(Binary::Sub, one, equal);
        b.ret(&[failure]);
    });
    program.define(main, |b, _| {
        let input = b.constant(wide, 511);
        let result = b.call(check, &[input]);
        b.ret(&result);
    });
    program
}

/// Runtime word parameters narrowed to Fixed0 and promoted back to Word.
/// Full-word comparisons check that both bytes are cleared even on the 6502.
#[must_use]
pub fn zero_conversion() -> Program {
    let (mut program, main) = Program::new("main");
    let check = program.declare("convert", &[Class::Word], &[Class::Word]);
    program.define(check, |b, args| {
        let narrowed = b.convert(Class::Fixed { bits: 0 }, args[0]);
        let promoted = b.convert(Class::Word, narrowed);
        let zero = b.constant(Class::Word, 0);
        let equal = b.compare(Relation::Equal, promoted, zero);
        b.ret(&[equal]);
    });
    program.define(main, |b, _| {
        let mut passed = b.constant(Class::Word, 0);
        for input in [0, 1, 255, 256, 65535] {
            let input = b.constant(Class::Word, input);
            let equal = b.call_one(check, &[input]);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(Class::Word, 5);
        let failures = b.binary(Binary::Sub, count, passed);
        b.ret(&[failures]);
    });
    program
}

/// Enough live products to occupy the 6502 home that once overlapped ARGC.
/// Arithmetic must preserve platform state, not only its own answers.
#[must_use]
pub fn preserves_host_count() -> Program {
    let (mut program, main) = Program::new("main");
    let argc = crate::platform::Routines::builtin().declare(&mut program, "argc");
    program.define(main, |b, _| {
        let before = b.call_one(argc, &[]);
        let two = b.constant(Class::Word, 2);
        let three = b.constant(Class::Word, 3);
        let products: Vec<_> = (0..12).map(|_| b.binary(Binary::Mul, two, three)).collect();
        let after = b.call_one(argc, &[]);
        let mut total = b.constant(Class::Word, 0);
        for product in products {
            total = b.binary(Binary::Add, total, product);
        }
        let expected = b.constant(Class::Word, 72);
        let correct = b.compare(Relation::Equal, total, expected);
        let preserved = b.compare(Relation::Equal, before, after);
        let passed = b.binary(Binary::Add, correct, preserved);
        let failures = b.binary(Binary::Sub, two, passed);
        b.ret(&[failures]);
    });
    program
}
