//! Target-specific limits and size baselines; conformance cases are shared.
use faun_core::targets::Target;

use crate::X86_64Linux;
use shared::{narrow, wide};

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[path = "float_tests.rs"]
mod float_tests;

#[path = "abi_tests.rs"]
mod abi_tests;

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: X86_64Linux = X86_64Linux;
const RUNNER: Option<&str> = None;

// Lower baselines when emission improves; explain any increase.
// Two-operand IMUL is one byte longer than implicit MUL in the shared
// intermediate rung, but no longer reserves/clobbers RAX/RCX/RDX. It removes
// register transfers in the runtime multiply and natural-number examples.
//
// A program that writes ignores `SIGPIPE` before anything else, so a write
// to a closed pipe answers `BrokenPipe` as it does on every other target:
// 25 bytes on every such program.
// An exit status is a `U8`, so an example whose status is worked out from a
// `Nat` takes it modulo 256; where the arm that bounds it is not seen to,
// that is real work.
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
    ("a shared intermediate", 157),
    ("a greeting", 182),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 127),
    ("two and two", 134),
    ("hello world", 183),
    ("a call", 143),
    ("recursion", 182),
    ("values across a call", 252),
    ("the heap", 178),
    ("a byte", 208),
    ("a global", 244),
    ("writing the heap", 221),
    ("a computed length", 225),
    ("eight bits", 133),
    ("less", 140),
    ("two worked out", 151),
    ("a flag", 219),
    ("a countdown", 191),
    ("a carried total", 156),
    ("a step first", 209),
    ("a long arm", 264),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 128),
    ("two-and-two", 128),
    ("double", 128),
    ("leave", 128),
    ("bool", 160),
    ("nat", 248),
    ("width", 156),
    ("argc", 169),
    ("expressions", 168),
    ("hello", 230),
];
const ARITHMETIC_SIZES: [usize; 3] = [165, 199, 198];

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
            ("a shared intermediate", 37),
            ("a greeting", 49),
        ]
    );
    assert_eq!(code[0].1, [0x31, 0xFF, 0x6A, 0x3C, 0x58, 0x0F, 0x05]);
    // The count's low byte, read straight from where the kernel left it.
    assert_eq!(
        code[1].1,
        [0x0F, 0xB6, 0x3C, 0x24, 0x6A, 0x3C, 0x58, 0x0F, 0x05]
    );
}

#[test]
fn it_holds_what_a_program_holds() {
    assert!(TARGET.accepts(&wide(70_000)).is_ok());
    assert!(TARGET.accepts(&wide(4)).is_ok());
    assert!(TARGET.accepts(&narrow(32)).is_ok());
}

#[test]
fn low_word_multiplication_preserves_unsigned_high_bits() {
    use faun_core::ir::{Binary, Class, Program, Relation};
    for (left, right) in [
        (u64::MAX, u64::MAX),
        (1 << 63, 3),
        (u64::from(u32::MAX), u64::from(u32::MAX)),
        (0, u64::MAX),
    ] {
        let (mut p, main) = Program::new("main");
        p.define(main, |b, _| {
            let a = b.constant(Class::Word, left);
            let c = b.constant(Class::Word, right);
            let product = b.binary(Binary::Mul, a, c);
            let expected = b.constant(Class::Word, left.wrapping_mul(right));
            let equal = b.compare(Relation::Equal, product, expected);
            b.ret(&[equal]);
        });
        assert_eq!(shared::status(&p), 1, "{left} * {right}");
    }
}
