//! Target-specific limits and size baselines; conformance cases are shared.
use faun::targets::Target;

use crate::Mos6502Sim65;
use shared::{narrow, wide};

#[path = "../../faun/tests/support/backend.rs"]
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
    ("the count under a guard", 54),
    ("the count and more", 56),
    ("a shared intermediate", 61),
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
    ("bool", 160),
    ("nat", 539),
    ("width", 56),
    ("argc", 56),
    ("expressions", 58),
];
const ARITHMETIC_SIZES: [usize; 3] = [209, 248, 246];

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
    let held = |program: &faun::ir::Program| {
        let artifacts = TARGET.compile(program).expect("scalar compilation");
        let code = 12 + program.data().len() + program.globals().len();
        artifacts[0].bytes[code..].starts_with(SETS_IT)
    };
    assert!(
        !held(&shared::read(shared::EXIT_ZERO).expect("a program")),
        "one that calls nothing"
    );
    assert!(
        held(&faun::programs::calls_a_function()),
        "one that calls something"
    );
    // A hook is reached by `jsr` like anything else, so asking the simulator
    // for something counts as calling something.
    assert!(held(&faun::programs::hello_world()), "one that writes");
}
