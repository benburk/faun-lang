//! Target-specific limits and size baselines; conformance cases are shared.
use faun_core::targets::Target;

use crate::{Mos6502Sim65, T0, T1};
use shared::{narrow, wide};

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: Mos6502Sim65 = Mos6502Sim65;
const RUNNER: Option<&str> = Some("sim65");

// Lower baselines when emission improves; explain any increase.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 17),
    ("the count", 33),
    ("the count and a constant", 36),
    ("the low bits of a sum", 34),
    ("the count under a guard", 43),
    ("the count and more", 48),
    ("a shared intermediate", 53),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 17),
    ("two and two", 40),
    ("hello world", 61),
    ("a call", 78),
    ("recursion", 232),
    ("values across a call", 390),
    ("the heap", 156),
    ("a byte", 213),
    ("a global", 142),
    ("writing the heap", 175),
    ("a computed length", 188),
    ("eight bits", 49),
    ("less", 59),
    ("two worked out", 83),
    ("a flag", 117),
    ("a countdown", 94),
    ("a carried total", 100),
    ("a step first", 94),
    ("a long arm", 982),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 17),
    ("two-and-two", 17),
    ("double", 17),
    ("leave", 17),
    ("bool", 154),
    ("nat", 473),
    ("width", 48),
    ("argc", 48),
    ("expressions", 50),
];
const ARITHMETIC_SIZES: [usize; 3] = [209, 248, 246];

fn code(program: &faun_core::ir::Program) -> Vec<u8> {
    TARGET.compile(program).expect("scalar compilation")[0]
        .bytes
        .clone()
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
        let artifacts = TARGET.compile(program).expect("scalar compilation");
        let code = 12 + program.data().len() + program.globals().len();
        artifacts[0].bytes[code..].starts_with(SETS_IT)
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
