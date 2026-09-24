//! Shared executable arithmetic checks.
//!
//! Calls take runtime parameters, not folded Barb constants. Each program returns zero only if every full-width
//! answer agrees, so checking an eight-bit process status loses no coverage.

use crate::ir::{Binary, Class, Direction, Program, Relation};

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
    let class = Class::fixed(bits);
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

/// Runtime byte products observed only after reduction modulo 256.
///
/// The product itself is wide enough for both inputs. Its explicit conversion
/// permits a target to calculate only the low byte; `Fixed` alone never makes
/// arithmetic wrap.
///
/// # Panics
/// If the fixed test corpus cannot fit in a machine word.
#[must_use]
pub fn byte_products() -> Program {
    let byte = Class::fixed(8);
    let product = Class::fixed(16);
    let (mut program, main) = Program::new("main");
    let check = program.declare("low_product", &[byte, byte, byte], &[Class::Word]);
    program.define(check, |b, args| {
        let wide = b.binary_at(product, Binary::Mul, args[0], args[1]);
        let low = b.convert(byte, wide);
        let equal = b.compare(Relation::Equal, low, args[2]);
        b.ret(&[equal]);
    });
    program.define(main, |b, _| {
        let cases: [(u64, u64); 7] = [
            (0, 255),
            (1, 255),
            (2, 128),
            (3, 85),
            (17, 17),
            (129, 2),
            (255, 255),
        ];
        let mut passed = b.constant(Class::Word, 0);
        for (left, right) in cases {
            let expected = (left * right) & 0xff;
            let args = [left, right, expected].map(|value| b.constant(byte, value));
            let equal = b.call_one(check, &args);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(cases.len()).expect("a few cases"),
        );
        let failures = b.binary(Binary::Sub, count, passed);
        b.ret(&[failures]);
    });
    program
}

/// Average two bytes in widened natural arithmetic.
///
/// The nine-bit sum is divided before the result returns to eight bits. This
/// differs from adding modulo 256 and then dividing whenever the sum carries.
///
/// # Panics
/// If the fixed test corpus cannot fit in a machine word.
#[must_use]
pub fn widened_byte_average() -> Program {
    let byte = Class::fixed(8);
    let sum = Class::fixed(9);
    let (mut program, main) = Program::new("main");
    let check = program.declare("average", &[byte, byte, byte], &[Class::Word]);
    program.define(check, |b, args| {
        let wide = b.binary_at(sum, Binary::Add, args[0], args[1]);
        let shifted = b.shift(sum, Direction::Down, wide, 1);
        let average = b.convert(byte, shifted);
        let equal = b.compare(Relation::Equal, average, args[2]);
        b.ret(&[equal]);
    });
    program.define(main, |b, _| {
        let cases: [(u64, u64); 7] = [
            (0, 0),
            (0, 255),
            (1, 2),
            (100, 200),
            (127, 129),
            (254, 255),
            (255, 255),
        ];
        let mut passed = b.constant(Class::Word, 0);
        for (left, right) in cases {
            let expected = left.midpoint(right);
            let args = [left, right, expected].map(|value| b.constant(byte, value));
            let equal = b.call_one(check, &args);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(cases.len()).expect("a few cases"),
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
    let small = Class::fixed(7);
    let wide = Class::fixed(15);
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
        let narrowed = b.convert(Class::fixed(0), args[0]);
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

/// A value added to itself, where the low byte carries into the high one.
///
/// A doubling is a shift, and a target that says so has to put the bit
/// leaving one byte into the next; only an input with a bit in the top of its
/// low byte says whether it does. The value arrives as a parameter, because
/// two constants are added before the program runs and nothing is shifted.
///
/// # Panics
/// If there are more cases than a count can hold.
#[must_use]
pub fn doubles_across_bytes() -> Program {
    let narrow = Class::fixed(15);
    let wide = Class::fixed(16);
    let (mut program, main) = Program::new("main");
    let check = program.declare("double", &[narrow, wide], &[Class::Word]);
    program.define(check, |b, args| {
        let doubled = b.binary_at(wide, Binary::Add, args[0], args[0]);
        let equal = b.compare(Relation::Equal, doubled, args[1]);
        b.ret(&[equal]);
    });
    program.define(main, |b, _| {
        let mut passed = b.constant(Class::Word, 0);
        // Nothing to carry, the lowest bit that carries, a byte of them, and
        // every bit the narrow class holds.
        let cases = [
            (0x0034, 0x0068),
            (0x0080, 0x0100),
            (0x00ff, 0x01fe),
            (0x7fff, 0xfffe),
        ];
        for (input, expected) in cases {
            let input = b.constant(narrow, input);
            let expected = b.constant(wide, expected);
            let equal = b.call_one(check, &[input, expected]);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(cases.len()).expect("a few cases"),
        );
        let failures = b.binary(Binary::Sub, count, passed);
        b.ret(&[failures]);
    });
    program
}

/// Products and quotients by powers of two, which every target has an
/// instruction for and reads as a shift.
///
/// The distances sit either side of a byte, because a target holding this in
/// two bytes moves the halves one at a time and the boundary between them is
/// where a bit has to cross. Going down, a value with bits below the
/// distance says they are dropped rather than carried anywhere.
///
/// # Panics
/// If there are more cases than a count can hold.
#[must_use]
pub fn shifts_by_powers_of_two() -> Program {
    const PLACES: [u32; 5] = [1, 2, 7, 8, 14];
    let wide = Class::fixed(16);
    let (mut program, main) = Program::new("main");
    let mut checks = vec![];
    for by in PLACES {
        let up = program.declare(&format!("up{by}"), &[wide, wide], &[Class::Word]);
        program.define(up, |b, args| {
            let places = b.constant(wide, 1 << by);
            let moved = b.binary_at(wide, Binary::Mul, args[0], places);
            let equal = b.compare(Relation::Equal, moved, args[1]);
            b.ret(&[equal]);
        });
        let down = program.declare(&format!("down{by}"), &[wide, wide], &[Class::Word]);
        program.define(down, |b, args| {
            let places = b.constant(wide, 1 << by);
            let moved = b.binary_at(wide, Binary::Div, args[0], places);
            let equal = b.compare(Relation::Equal, moved, args[1]);
            b.ret(&[equal]);
        });
        checks.push((by, up, down));
    }
    program.define(main, |b, _| {
        let mut passed = b.constant(Class::Word, 0);
        for &(by, up, down) in &checks {
            // Three, so that going up puts a bit in every byte it reaches.
            let args = [b.constant(wide, 3), b.constant(wide, 3 << by)];
            let answer = b.call_one(up, &args);
            passed = b.binary(Binary::Add, passed, answer);
            // Odd and high, so that going down drops bits off the bottom and
            // brings bits across the boundary.
            let args = [b.constant(wide, 0xBEEF), b.constant(wide, 0xBEEF >> by)];
            let answer = b.call_one(down, &args);
            passed = b.binary(Binary::Add, passed, answer);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(2 * checks.len()).expect("a few cases"),
        );
        let failures = b.binary(Binary::Sub, count, passed);
        b.ret(&[failures]);
    });
    program
}

/// A byte doubled, and then the number it was doubled from read again.
///
/// Doubling a byte can be one shift, which leaves an answer where the number
/// that went in was. A target keeping track of what it has to hand has to say
/// so, or the next read of that same number is left out as already there and
/// the shifted answer stands in for it. Every operand here is known before
/// the program runs on purpose: it is the number believed to be to hand that
/// goes stale, so a runtime one would not say this.
#[must_use]
pub fn doubles_then_reads_the_same_number() -> Program {
    let byte = Class::fixed(8);
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let two = b.constant(byte, 2);
        let doubled = b.binary_at(byte, Binary::Add, two, two);
        let five = b.constant(byte, 5);
        let apart = b.binary_at(byte, Binary::Add, two, five);
        let total = b.binary_at(byte, Binary::Add, doubled, apart);
        let expected = b.constant(byte, 11);
        let wrong = b.binary_at(byte, Binary::Sub, total, expected);
        let wrong = b.convert(Class::Word, wrong);
        b.ret(&[wrong]);
    });
    program
}

/// Enough live products to occupy the 6502 home that once overlapped ARGC.
/// Arithmetic must preserve platform state, not only its own answers: the
/// count, run as one, is read after every product.
#[must_use]
pub fn preserves_host_count() -> Program {
    let (mut program, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
    program.define(main, |b, params| {
        let argc = params[0];
        let two = b.constant(Class::Word, 2);
        let three = b.constant(Class::Word, 3);
        let products: Vec<_> = (0..12).map(|_| b.binary(Binary::Mul, two, three)).collect();
        let one = b.constant(Class::Word, 1);
        let mut total = b.constant(Class::Word, 0);
        for product in products {
            total = b.binary(Binary::Add, total, product);
        }
        let expected = b.constant(Class::Word, 72);
        let correct = b.compare(Relation::Equal, total, expected);
        let preserved = b.compare(Relation::Equal, argc, one);
        let passed = b.binary(Binary::Add, correct, preserved);
        let failures = b.binary(Binary::Sub, two, passed);
        b.ret(&[failures]);
    });
    program
}
