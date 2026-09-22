//! Target-specific limits and size baselines; conformance cases are shared.
use faun::targets::Target;

use crate::X86_64Linux;
use shared::{narrow, wide};

#[path = "../../faun/tests/support/backend.rs"]
mod shared;

const TARGET: X86_64Linux = X86_64Linux;
const RUNNER: Option<&str> = None;

// Lower baselines when emission improves; explain any increase.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 127),
    ("the count", 135),
    ("the count and a constant", 148),
    ("the low bits of a sum", 145),
    ("the count under a guard", 166),
    ("the count and more", 171),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 127),
    ("two and two", 134),
    ("hello world", 158),
    ("a call", 143),
    ("recursion", 200),
    ("values across a call", 256),
    ("the heap", 178),
    ("a byte", 209),
    ("a global", 246),
    ("writing the heap", 196),
    ("a computed length", 205),
    ("eight bits", 142),
    ("less", 142),
    ("two worked out", 169),
    ("a flag", 221),
    ("a countdown", 199),
    ("a carried total", 169),
    ("a step first", 206),
    ("a long arm", 277),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 128),
    ("two-and-two", 128),
    ("double", 128),
    ("leave", 128),
    ("bool", 212),
    ("nat", 537),
    ("width", 170),
    ("argc", 196),
    ("expressions", 197),
];
const ARITHMETIC_SIZES: [usize; 3] = [204, 215, 216];

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(70_000)).is_ok());
    assert!(TARGET.accepts(&wide(4)).is_ok());
    assert!(TARGET.accepts(&narrow(32)).is_ok());
}
