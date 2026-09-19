//! Target-specific limits and size baselines; conformance cases are shared.
use faun::targets::Target;

use crate::X86_64Linux;
use shared::{narrow, wide};

#[path = "../../faun/tests/support/backend.rs"]
mod shared;

const TARGET: X86_64Linux = X86_64Linux;
const RUNNER: Option<&str> = None;

// Lower baselines when emission improves; explain any increase.
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("empty", 127),
    ("exit zero", 127),
    ("two and two", 134),
    ("hello world", 158),
    ("a call", 156),
    ("recursion", 245),
    ("values across a call", 267),
    ("the heap", 193),
    ("a byte", 241),
    ("a global", 256),
    ("writing the heap", 206),
    ("a computed length", 225),
    ("eight bits", 142),
    ("less", 143),
    ("two worked out", 171),
    ("a flag", 257),
    ("a countdown", 217),
    ("a carried total", 281),
    ("a step first", 230),
    ("a long arm", 332),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 128),
    ("two-and-two", 128),
    ("double", 128),
    ("leave", 128),
    ("bool", 337),
    ("nat", 891),
    ("width", 281),
    ("argc", 298),
];
const ARITHMETIC_SIZES: [usize; 3] = [224, 235, 236];

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(70_000)).is_ok());
    assert!(TARGET.accepts(&wide(4)).is_ok());
    assert!(TARGET.accepts(&narrow(32)).is_ok());
}
