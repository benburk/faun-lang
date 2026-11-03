//! Target-specific limits and size baselines; conformance cases are shared.
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use faun_core::ir::{Binary, Class, FunctionId, Offset, Program, Relation, Width};
use faun_core::targets::Target;

use crate::{Mos6502Sim65, T0, T1};
use shared::{narrow, wide};

#[path = "../../core/tests/support/backend.rs"]
mod shared;

const TARGET: Mos6502Sim65 = Mos6502Sim65;
const RUNNER: Option<&str> = Some("sim65");

// Lower baselines when emission improves; explain any increase.
//
// An exit status is a `U8`, so an example whose status is worked out from a
// `Nat` takes it modulo 256; where the arm that bounds it is not seen to,
// that is real work.
/// The ladder of simplest programs, from Barb. Lower these when the
/// compiler improves; a rise is the compiler getting worse at the one
/// thing small enough to read.
const LADDER_SIZES: &[(&str, usize)] = &[
    ("a constant", 17),
    ("the count", 31),
    ("the count and a constant", 34),
    ("the low bits of a sum", 32),
    ("the count under a guard", 41),
    ("the count and more", 46),
    ("a shared intermediate", 51),
    ("a greeting", 51),
];
// A program that grows its heap pays 38 bytes for `grow` refusing to pass
// the frames, and for the frame pointer being set for it to be measured
// against, which is what lets the heap have all the memory the frames leave.
// A program whose calls can go round says `stack overflow` on standard error
// and exits with status 3 where its calls run out of stack, rather than
// wrapping the hardware stack and hanging: 39 bytes on every such program
// for the routine, the arguments it hands `write` and the message, and 5
// on each function in a cycle, which checks the stack pointer on the way in.
const CORPUS_SIZES: &[(&str, usize)] = &[
    ("exit zero", 17),
    ("two and two", 40),
    ("hello world", 61),
    ("a call", 78),
    ("recursion", 263),
    ("values across a call", 390),
    ("the heap", 194),
    ("a byte", 251),
    ("a global", 142),
    ("writing the heap", 213),
    ("a computed length", 226),
    ("eight bits", 49),
    ("less", 53),
    ("two worked out", 83),
    ("a flag", 98),
    ("a countdown", 86),
    ("a carried total", 82),
    ("a step first", 86),
    ("a long arm", 559),
];
const EXAMPLE_SIZES: &[(&str, usize)] = &[
    ("exit", 17),
    ("two-and-two", 17),
    ("double", 17),
    ("leave", 17),
    ("bool", 81),
    ("nat", 170),
    ("width", 52),
    ("argc", 63),
    ("expressions", 62),
    ("hello", 204),
];
const ARITHMETIC_SIZES: [usize; 3] = [209, 247, 245];

fn code(program: &Program) -> Vec<u8> {
    TARGET
        .compile_machine_ir(program)
        .expect("scalar compilation")
}

#[test]
fn byte_arithmetic_uses_the_6502_carry_and_early_exit_loop() {
    // White Flame's fifteen-byte loop: initialize A, enter at the multiplier
    // shift, and leave as soon as its remaining bits are zero.
    const BYTE_MULTIPLY: &[u8] = &[
        0xA9, 0x00, 0xF0, 0x05, 0x18, 0x65, T0, 0x06, T0, 0x46, T1, 0xB0, 0xF7, 0xD0, 0xF8,
    ];
    let product = code(&faun_core::programs::arithmetic::byte_products());
    assert!(
        product
            .windows(BYTE_MULTIPLY.len())
            .any(|bytes| bytes == BYTE_MULTIPLY),
        "low-byte products should use the fifteen-byte loop"
    );

    let average = code(&faun_core::programs::arithmetic::widened_byte_average());
    assert!(
        average
            .windows(6)
            .any(|bytes| { matches!(bytes, [0x18, 0x65, _, 0x6A, 0x85, _]) }),
        "a widened byte sum should rotate its carry directly into the quotient"
    );
}

#[test]
fn narrow_equality_does_not_compare_known_zero_high_bytes() {
    let code = code(&faun_core::programs::arithmetic::widened_byte_average());
    assert!(
        code.windows(2).any(|bytes| matches!(bytes, [0xC5, _])),
        "the fixture should compare its byte result"
    );
    assert!(
        !code
            .windows(4)
            .any(|bytes| bytes == [0xA9, 0x00, 0xC9, 0x00]),
        "equal known high bytes need no comparison"
    );
}

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
    let held = |program: &Program| {
        let image = TARGET
            .compile_machine_ir(program)
            .expect("scalar compilation");
        let code = 12 + crate::globals_offset(program) + program.globals().len();
        image[code..].starts_with(SETS_IT)
    };
    assert!(
        !held(&shared::read(shared::EXIT_ZERO).expect("a program")),
        "one that calls nothing"
    );
    assert!(
        held(&faun_core::programs::calls_a_function()),
        "one that calls something"
    );
    // A hook is reached by `jsr` like anything else, so asking the simulator
    // for something counts as calling something.
    assert!(held(&faun_core::programs::hello_world()), "one that writes");
}

/// Prepare `program` and run it under the simulator: its status, what it
/// wrote on standard output, and what it wrote on standard error.
///
/// # Panics
///
/// If it has not finished in ten seconds, which is a program that hangs.
fn run_reporting(program: &Program) -> (Option<i32>, String, String) {
    let dir = std::env::temp_dir().join(format!(
        "faun-sim65-stack-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("a clock after the epoch")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("a directory to run in");
    let prepared = TARGET
        .prepare(program)
        .expect("a program this machine holds");
    let image = TARGET.emit(&prepared);
    let path = TARGET
        .write(&image, &dir.join("program"))
        .expect("somewhere to write it");
    let mut child = Command::new(RUNNER.expect("a simulator"))
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("a machine to run it");
    let started = Instant::now();
    while child.try_wait().expect("a machine to ask").is_none() {
        if started.elapsed() > Duration::from_secs(10) {
            child.kill().expect("a machine to stop");
            panic!("the program hung");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().expect("a machine to finish");
    std::fs::remove_dir_all(&dir).expect("the scratch directory to go");
    let stdout = String::from_utf8(output.stdout).expect("what it wrote, as text");
    let stderr = String::from_utf8(output.stderr).expect("what it said, as text");
    (output.status.code(), stdout, stderr)
}

/// Assert that `program` ends saying its stack overflowed, and nothing else.
fn says_stack_overflow(program: &Program) {
    let (status, stdout, stderr) = run_reporting(program);
    assert_eq!(stdout, "");
    assert_eq!(stderr, "stack overflow\n");
    assert_eq!(status, Some(3));
}

/// A function counting `n` down to nought through calls to itself, keeping
/// `kept` products of `n` across each call: each is a slot in its frame.
fn define_countdown(program: &mut Program, kept: u64) -> FunctionId {
    let down = program.declare("down", &[Class::Word], &[Class::Word]);
    program.define(down, |b, params| {
        let n = params[0];
        let zero = b.constant(Class::Word, 0);
        let done = b.compare(Relation::Equal, n, zero);
        let answer = b.if_(
            done,
            &[Class::Word],
            |b| {
                let zero = b.constant(Class::Word, 0);
                b.yield_(&[zero]);
            },
            |b| {
                let mut products = Vec::new();
                for step in 1..=kept {
                    let step = b.constant(Class::Word, step);
                    let product = b.binary(Binary::Mul, n, step);
                    products.push(product);
                }
                let one = b.constant(Class::Word, 1);
                let less = b.binary(Binary::Sub, n, one);
                let rest = b.call(down, &[less]);
                let mut total = rest[0];
                for product in products {
                    total = b.binary(Binary::Add, total, product);
                }
                b.yield_(&[total]);
            },
        );
        b.ret(&answer);
    });
    down
}

/// A call going deeper than the hardware stack has room for, 128 return
/// addresses, ends the program saying so on standard error, with a status
/// of its own, rather than wrapping the stack and hanging.
#[test]
fn a_call_too_deep_for_the_stack_says_so() {
    let program = shared::read(
        "import std.host {Host}

         again : Nat -> Nat
         again(0) -> 0
         again(Succ(n)) -> again(n) + 1

         main! : Host -> []
         main!(host) -> (
           host.println!(again(200 + host.args.len()).to_str())
           host.exit!(0)
         )",
    )
    .expect("a program");
    says_stack_overflow(&program);
}

/// Frames reaching down into a heap that has taken the rest of memory are
/// the stack running out as well, and say so, rather than ending with the
/// status a heap with no more room ends with.
#[test]
fn frames_meeting_the_heap_say_the_stack_overflowed() {
    let (mut program, main) = Program::new("main");
    let grow = faun_core::platform::Routines::builtin().declare(&mut program, "grow");
    let down = define_countdown(&mut program, 1);
    // The heap takes all it can, a little at a time, until `grow` answers
    // that nothing more fits; then calls go a hundred deep, well within
    // what the hardware stack holds.
    program.define(main, |b, _| {
        b.loop_(&[], &[], |b, _| {
            let size = b.constant(Class::Word, 32);
            let page = b.call_one(grow, &[size]);
            let page = b.convert(Class::Word, page);
            let refused = b.constant(Class::Word, 0xFFFF);
            let full = b.compare(Relation::Equal, page, refused);
            b.if_(full, &[], |b| b.break_(&[]), |b| b.continue_(&[]));
        });
        let hundred = b.constant(Class::Word, 100);
        let answer = b.call(down, &[hundred]);
        b.ret(&answer);
    });
    says_stack_overflow(&program);
}

/// Where nothing grows a heap, frames reaching down into the image are the
/// stack running out too, and say so, before they write over the code.
/// Each call here keeps two hundred values across the next, and data fills
/// half of memory, so the frames run out long before the hardware stack.
#[test]
fn frames_reaching_the_image_say_the_stack_overflowed() {
    let (mut program, main) = Program::new("main");
    let down = define_countdown(&mut program, 200);
    program.define(main, |b, _| {
        let filler = b.data(&vec![1; 0x7000]);
        let at = b.address_of(filler);
        let one = b.load(Width::Byte, at, Offset::Bytes(0));
        let hundred = b.constant(Class::Word, 100);
        let depth = b.binary(Binary::Add, hundred, one);
        let answer = b.call(down, &[depth]);
        b.ret(&answer);
    });
    says_stack_overflow(&program);
}
