//! Target-specific limits and size baselines; conformance cases are shared.
use faun::targets::Target;

use crate::Mos6502Sim65;
use shared::{narrow, wide};

#[path = "../../faun/tests/support/backend.rs"]
mod shared;

const TARGET: Mos6502Sim65 = Mos6502Sim65;
const RUNNER: Option<&str> = Some("sim65");

// Lower baselines when emission improves; explain any increase.
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("empty", 30),
    ("exit zero", 20),
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
    ("eight bits", 81),
    ("less", 63),
    ("two worked out", 89),
    ("a flag", 119),
    ("a countdown", 96),
    ("a carried total", 102),
    ("a step first", 99),
    ("a long arm", 1008),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 20),
    ("two-and-two", 20),
    ("double", 20),
    ("leave", 20),
    ("bool", 203),
    ("nat", 879),
    ("width", 196),
    ("argc", 239),
    ("expressions", 180),
];
const ARITHMETIC_SIZES: [usize; 3] = [209, 248, 248];

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
