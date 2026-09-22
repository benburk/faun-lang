//! Target-specific limits and size baselines; conformance cases are shared.
use faun_core::programs;
use faun_core::targets::Target;

use crate::Wasm32Wasi;
use shared::{EXIT_ZERO, bytes, execute, narrow, read, status, wide};

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: Wasm32Wasi = Wasm32Wasi;
const RUNNER: Option<&str> = Some("wasmtime");

// Lower baselines when emission improves; explain any increase.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 36),
    ("the count", 158),
    ("the count and a constant", 181),
    ("the low bits of a sum", 181),
    ("the count under a guard", 184),
    ("the count and more", 191),
    ("a shared intermediate", 198),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 36),
    ("two and two", 105),
    ("hello world", 141),
    ("a call", 125),
    ("recursion", 159),
    ("values across a call", 204),
    ("the heap", 137),
    ("a byte", 160),
    ("a global", 158),
    ("writing the heap", 163),
    ("a computed length", 170),
    ("eight bits", 118),
    ("less", 105),
    ("two worked out", 119),
    ("a flag", 135),
    ("a countdown", 173),
    ("a carried total", 156),
    ("a step first", 172),
    ("a long arm", 401),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 96),
    ("two-and-two", 96),
    ("double", 96),
    ("leave", 96),
    ("bool", 228),
    ("nat", 406),
    ("width", 191),
    ("argc", 191),
    ("expressions", 198),
];
const ARITHMETIC_SIZES: [usize; 3] = [156, 164, 162];

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(70_000)).is_ok());
    assert!(TARGET.accepts(&wide(4)).is_ok());
    assert!(TARGET.accepts(&narrow(32)).is_ok());
    let refused = TARGET.accepts(&narrow(33)).unwrap_err();
    assert!(
        refused.contains("holds 32 bits, and a value here needs 33"),
        "{refused}"
    );
}

/// `proc_exit(0)` at the end of the entry needs no import, memory or data.
#[test]
fn the_smallest_module_imports_nothing() {
    assert_eq!(execute(&programs::empty()).1, "");
    let written = read(EXIT_ZERO).expect("a program");
    assert_eq!(bytes(&written), bytes(&programs::empty()));
}

/// WASM uses its operand stack for multiple returns and region transfers.
#[test]
fn multivalue_function_and_region_abis_are_supported() {
    assert_eq!(status(&programs::abi::function(7, 3)), 0);
    for kind in [
        programs::abi::Transfer::If,
        programs::abi::Transfer::LoopState,
        programs::abi::Transfer::LoopResults,
    ] {
        assert_eq!(status(&programs::abi::region(kind, 3)), 0);
    }
}
