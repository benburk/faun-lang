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
//
// An exit status is a `U8`, so an example whose status is worked out from a
// `Nat` takes it modulo 256; where the arm that bounds it is not seen to,
// that is real work.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 36),
    ("the count", 152),
    ("the count and a constant", 159),
    ("the low bits of a sum", 159),
    ("the count under a guard", 170),
    ("the count and more", 173),
    ("a shared intermediate", 176),
    ("a greeting", 140),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 36),
    ("two and two", 99),
    ("hello world", 141),
    ("a call", 113),
    ("recursion", 141),
    ("values across a call", 168),
    ("the heap", 131),
    ("a byte", 150),
    ("a global", 148),
    ("writing the heap", 161),
    ("a computed length", 168),
    ("eight bits", 104),
    ("less", 99),
    ("two worked out", 113),
    ("a flag", 131),
    ("a countdown", 165),
    ("a carried total", 152),
    ("a step first", 168),
    ("a long arm", 237),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 96),
    ("two-and-two", 96),
    ("double", 96),
    ("leave", 96),
    ("bool", 196),
    ("nat", 314),
    ("width", 179),
    ("argc", 190),
    ("expressions", 191),
    ("hello", 254),
];
const ARITHMETIC_SIZES: [usize; 3] = [142, 150, 148];

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
