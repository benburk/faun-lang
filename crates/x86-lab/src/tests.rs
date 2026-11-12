//! Target-specific limits and size baselines; conformance cases are shared.
use crate::targets::Target;

use crate::X86_64Linux;
use shared::{narrow, wide};

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[path = "float_tests.rs"]
mod float_tests;

#[path = "abi_tests.rs"]
mod abi_tests;

mod layout;
mod runtime_lifetimes;
mod runtime_naturals;

use crate as backend_core;
#[path = "test_frontend.rs"]
mod faun;

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: X86_64Linux = X86_64Linux;
const RUNNER: Option<&str> = None;

// Lower baselines when emission improves; explain any increase.
// Two-operand IMUL does not reserve or clobber RAX/RCX/RDX, which removes
// register transfers in the runtime multiply and natural-number examples. A
// known multiplier is taken into the instruction: three, five and nine as a
// LEA, which also takes a number added next.
//
// A program that writes ignores `SIGPIPE` before anything else, so a write
// to a closed pipe answers `BrokenPipe` as it does on every other target:
// 21 bytes on every such program, and 4 more to put the stack back where
// it reads its arguments.
// A program whose calls can go round handles the fault at the end of its
// stack, saying `stack overflow` and exiting with status 3 rather than
// ending with `SIGSEGV` and nothing said: 129 bytes on every such program,
// 25 of them telling that fault from any other.
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
    ("the count under a guard", 137),
    ("the count and more", 142),
    ("a shared intermediate", 143),
    ("a greeting", 178),
];
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 127),
    ("two and two", 131),
    ("hello world", 179),
    ("a call", 143),
    ("recursion", 311),
    ("values across a call", 252),
    ("the heap", 178),
    ("a byte", 208),
    ("a global", 244),
    ("writing the heap", 217),
    ("a computed length", 221),
    ("eight bits", 133),
    ("less", 140),
    ("two worked out", 151),
    ("a flag", 216),
    ("a countdown", 187),
    ("a carried total", 156),
    ("a step first", 205),
    ("a long arm", 261),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 128),
    ("two-and-two", 128),
    ("double", 128),
    ("leave", 128),
    ("bool", 157),
    ("nat", 253),
    ("width", 153),
    ("argc", 163),
    ("expressions", 162),
    ("hello", 226),
];
const ARITHMETIC_SIZES: [usize; 3] = [165, 199, 198];

#[test]
fn ladder_code_size_ratchets() {
    let routines = TARGET.routines();
    let mut code = Vec::new();
    for (name, mut barb) in crate::programs::ladder::every() {
        faun_core::barb::optimize(&mut barb);
        let machine = crate::lower_to_machine_ir(&barb, &routines).unwrap();
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
            ("the count under a guard", 17),
            ("the count and more", 22),
            ("a shared intermediate", 23),
            ("a greeting", 45),
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
    use crate::ir::{Binary, Class, Program, Relation};
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

/// A recursion's way out, which touches nothing it keeps for its caller,
/// returns without saving it, favouring speed; favouring size, the frame
/// opens where the function starts.
#[test]
fn an_early_way_out_saves_nothing() {
    use crate::machine::Inst;
    use faun_core::targets::Favour;
    let program = TARGET.prepare(&crate::programs::recurses()).unwrap();
    let first = |favour| {
        let allocated =
            crate::selected::select_and_allocate_favouring(&program, favour, false).unwrap();
        let (_, start) = allocated
            .functions()
            .find(|&(function, _)| function != program.entry())
            .unwrap();
        allocated.instructions()[start]
    };
    assert!(!matches!(first(Favour::Speed), Inst::OpenFrame { .. }));
    assert!(matches!(first(Favour::Size), Inst::OpenFrame { .. }));
}

/// Written with its symbols, a program is one to profile: every function
/// but the entry pushes `rbp` and points it at its frame where it starts,
/// and gives it back before each way out. The entry pushes nothing, Linux
/// starting it with `rbp` nought, which ends the chain.
#[test]
fn a_program_written_with_symbols_chains_its_frames() {
    use crate::machine::{Inst, Reg, RegisterWidth};
    use faun_core::targets::Favour;
    let program = TARGET.prepare(&crate::programs::recurses()).unwrap();
    for favour in [Favour::Speed, Favour::Size] {
        let allocated =
            crate::selected::select_and_allocate_favouring(&program, favour, true).unwrap();
        let code = allocated.instructions();
        for (function, start) in allocated.functions() {
            if function == program.entry() {
                assert_ne!(code[start], Inst::PushRegister { src: Reg::Rbp });
            } else {
                assert_eq!(
                    code[start..start + 2],
                    [
                        Inst::PushRegister { src: Reg::Rbp },
                        Inst::Move {
                            dst: Reg::Rbp,
                            src: Reg::Rsp,
                            width: RegisterWidth::Word,
                        },
                    ]
                );
            }
        }
        for (at, inst) in code.iter().enumerate() {
            if *inst == Inst::Return {
                assert_eq!(code[at - 1], Inst::Pop { dst: Reg::Rbp }, "{favour:?}");
            }
        }
    }
}

/// And it answers what it answers without them, its frames chained or not:
/// a function reading arguments its caller left on the stack finds them a
/// word further up.
#[test]
fn chaining_frames_changes_no_answer() {
    use faun_core::targets::{Favour, SymbolTable};
    let mut programs = vec![
        crate::programs::recurses(),
        crate::programs::values_survive_a_call(),
        crate::programs::calls_a_function(),
    ];
    programs.extend(
        crate::programs::printing()
            .into_iter()
            .map(|(_, program, _)| program),
    );
    for program in programs {
        let program = TARGET.prepare(&program).unwrap();
        let run = |symbols| {
            let dir = std::env::temp_dir().join(format!(
                "faun-frames-{}-{symbols:?}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir_all(&dir).unwrap();
            let image = TARGET.emit_with(&program, Favour::Speed, symbols);
            let path = TARGET.write(&image, &dir.join("program")).unwrap();
            let output = std::process::Command::new(&path).output().unwrap();
            std::fs::remove_dir_all(&dir).unwrap();
            (output.status.code(), output.stdout)
        };
        assert_eq!(run(SymbolTable::Omitted), run(SymbolTable::Written));
    }
}
