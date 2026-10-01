//! Target-specific limits and size baselines; conformance cases are shared.
use faun_core::targets::Target;

use crate::{Mos6502Sim65, T0, T1};
use shared::{narrow, wide};

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: Mos6502Sim65 = Mos6502Sim65;
const RUNNER: Option<&str> = Some("sim65");

// Lower baselines when emission improves; explain any increase.
//
// An exit status is a `U8`, so an example whose status is worked out from a
// `Nat` takes it modulo 256; where the arm that bounds it is not seen to,
// that is real work.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 17),
    ("the count", 31),
    ("the count and a constant", 34),
    ("the low bits of a sum", 32),
    ("the count under a guard", 41),
    ("the count and more", 46),
    ("a shared intermediate", 51),
    ("a greeting", 51),
];
// A program that grows its heap pays 38 bytes for `grow` refusing to pass
// the frames, and for the frame pointer being set for it to be measured
// against, which is what lets the heap have all the memory the frames leave.
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 17),
    ("two and two", 40),
    ("hello world", 61),
    ("a call", 78),
    ("recursion", 220),
    ("values across a call", 390),
    ("the heap", 194),
    ("a byte", 251),
    ("a global", 142),
    ("writing the heap", 213),
    ("a computed length", 226),
    ("eight bits", 49),
    ("less", 53),
    ("two worked out", 83),
    ("a flag", 98),
    ("a countdown", 86),
    ("a carried total", 82),
    ("a step first", 86),
    ("a long arm", 559),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 17),
    ("two-and-two", 17),
    ("double", 17),
    ("leave", 17),
    ("bool", 81),
    ("nat", 189),
    ("width", 52),
    ("argc", 63),
    ("expressions", 62),
    ("hello", 204),
];
const ARITHMETIC_SIZES: [usize; 3] = [209, 247, 245];

fn code(program: &faun_core::ir::Program) -> Vec<u8> {
    TARGET
        .compile_machine_ir(program)
        .expect("scalar compilation")
}

#[test]
fn byte_arithmetic_uses_the_6502_carry_and_early_exit_loop() {
    // White Flame's fifteen-byte loop: initialize A, enter at the multiplier
    // shift, and leave as soon as its remaining bits are zero.
    const BYTE_MULTIPLY: &[u8] = &[
        0xA9, 0x00, 0xF0, 0x05, 0x18, 0x65, T0, 0x06, T0, 0x46, T1, 0xB0, 0xF7, 0xD0, 0xF8,
    ];
    let product = code(&faun_core::programs::arithmetic::byte_products());
    assert!(
        product
            .windows(BYTE_MULTIPLY.len())
            .any(|bytes| bytes == BYTE_MULTIPLY),
        "low-byte products should use the fifteen-byte loop"
    );

    let average = code(&faun_core::programs::arithmetic::widened_byte_average());
    assert!(
        average
            .windows(6)
            .any(|bytes| { matches!(bytes, [0x18, 0x65, _, 0x6A, 0x85, _]) }),
        "a widened byte sum should rotate its carry directly into the quotient"
    );
}

#[test]
fn narrow_equality_does_not_compare_known_zero_high_bytes() {
    let code = code(&faun_core::programs::arithmetic::widened_byte_average());
    assert!(
        code.windows(2).any(|bytes| matches!(bytes, [0xC5, _])),
        "the fixture should compare its byte result"
    );
    assert!(
        !code
            .windows(4)
            .any(|bytes| bytes == [0xA9, 0x00, 0xC9, 0x00]),
        "equal known high bytes need no comparison"
    );
}

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(4)).is_ok());
    let refused = TARGET.accepts(&wide(70_000)).unwrap_err();
    assert!(refused.contains("holds 16 bits, and 70000"), "{refused}");
    let refused = TARGET.accepts(&narrow(32)).unwrap_err();
    assert!(
        refused.contains("holds 16 bits, and a value here needs 32"),
        "{refused}"
    );
}

/// Setting the stack pointer costs three bytes, and there is no cheaper way
/// to reach a known one: nothing may assume where the simulator left it, and
/// `X` is the only thing it can be set from. What a program can do is not
/// need one -- nothing here pushes but `jsr`, so one that calls nothing has
/// nothing to push.
#[test]
fn only_a_program_that_calls_something_sets_the_stack() {
    // ldx #$FF, txs.
    const SETS_IT: &[u8] = &[0xA2, 0xFF, 0x9A];
    let held = |program: &faun_core::ir::Program| {
        let image = TARGET
            .compile_machine_ir(program)
            .expect("scalar compilation");
        let code = 12 + crate::globals_offset(program) + program.globals().len();
        image[code..].starts_with(SETS_IT)
    };
    assert!(
        !held(&shared::read(shared::EXIT_ZERO).expect("a program")),
        "one that calls nothing"
    );
    assert!(
        held(&faun_core::programs::calls_a_function()),
        "one that calls something"
    );
    // A hook is reached by `jsr` like anything else, so asking the simulator
    // for something counts as calling something.
    assert!(held(&faun_core::programs::hello_world()), "one that writes");
}
