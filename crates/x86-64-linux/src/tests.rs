//! Target-specific limits and size baselines; conformance cases are shared.
use faun_core::targets::Target;

use crate::X86_64Linux;
use shared::{narrow, wide};

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: X86_64Linux = X86_64Linux;
const RUNNER: Option<&str> = None;

// Lower baselines when emission improves; explain any increase.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 127),
    ("the count", 129),
    ("the count and a constant", 132),
    ("the low bits of a sum", 131),
    ("the count under a guard", 147),
    ("the count and more", 150),
    ("a shared intermediate", 156),
    ("a greeting", 157),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 127),
    ("two and two", 134),
    ("hello world", 158),
    ("a call", 143),
    ("recursion", 189),
    ("values across a call", 256),
    ("the heap", 178),
    ("a byte", 208),
    ("a global", 244),
    ("writing the heap", 196),
    ("a computed length", 200),
    ("eight bits", 133),
    ("less", 140),
    ("two worked out", 169),
    ("a flag", 219),
    ("a countdown", 166),
    ("a carried total", 154),
    ("a step first", 191),
    ("a long arm", 264),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 128),
    ("two-and-two", 128),
    ("double", 128),
    ("leave", 128),
    ("bool", 157),
    ("nat", 381),
    ("width", 145),
    ("argc", 145),
    ("expressions", 151),
    ("hello", 214),
];
const ARITHMETIC_SIZES: [usize; 3] = [201, 212, 211];

#[test]
fn ladder_code_size_ratchets() {
    let routines = TARGET.routines();
    let mut code = Vec::new();
    for (name, mut barb) in faun_core::programs::ladder::every() {
        faun_core::barb::optimize(&mut barb);
        let machine = faun_core::lower_to_machine_ir(&mut barb, &routines).unwrap();
        let prepared = TARGET.prepare(&machine).unwrap();
        let allocated = crate::selected::select_and_allocate(&prepared).unwrap();
        code.push((name, crate::encode::encode(&allocated).bytes));
    }

    let sizes: Vec<_> = code
        .iter()
        .map(|(name, bytes)| (*name, bytes.len()))
        .collect();
    assert_eq!(
        sizes,
        [
            ("a constant", 7),
            ("the count", 9),
            ("the count and a constant", 12),
            ("the low bits of a sum", 11),
            ("the count under a guard", 27),
            ("the count and more", 30),
            ("a shared intermediate", 36),
            ("a greeting", 24),
        ]
    );
    assert_eq!(code[0].1, [0x31, 0xFF, 0x6A, 0x3C, 0x58, 0x0F, 0x05]);
    assert_eq!(
        code[1].1,
        [0x48, 0x8B, 0x3C, 0x24, 0x6A, 0x3C, 0x58, 0x0F, 0x05]
    );
}

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(70_000)).is_ok());
    assert!(TARGET.accepts(&wide(4)).is_ok());
    assert!(TARGET.accepts(&narrow(32)).is_ok());
}
