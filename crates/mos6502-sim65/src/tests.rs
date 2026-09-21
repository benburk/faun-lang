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
    ("the count", 44),
    ("the count and more", 77),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("empty", 30),
    ("exit zero", 17),
    ("two and two", 45),
    ("hello world", 63),
    ("a call", 81),
    ("recursion", 232),
    ("values across a call", 390),
    ("the heap", 158),
    ("a byte", 215),
    ("a global", 144),
    ("writing the heap", 177),
    ("a computed length", 190),
    ("eight bits", 63),
    ("less", 61),
    ("two worked out", 89),
    ("a flag", 119),
    ("a countdown", 96),
    ("a carried total", 102),
    ("a step first", 99),
    ("a long arm", 991),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 17),
    ("two-and-two", 17),
    ("double", 17),
    ("leave", 17),
    ("bool", 169),
    ("nat", 570),
    ("width", 82),
    ("argc", 91),
    ("expressions", 82),
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
