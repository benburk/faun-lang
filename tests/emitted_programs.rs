//! Compile for each target, then actually run the result.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, PoisonError};

use faun::ir::Class::Word;
use faun::ir::{Binary, Builder, Class, Offset, Program, Relation, Width};
use faun::targets::Target;

/// The whole of a program that does nothing: a number to leave with, and the
/// one effect there is. This is the floor for a program somebody writes,
/// where [`empty`] is the floor for one this tier is handed.
const EXIT_ZERO: &str = "type Nat Zero Succ(Nat)

                         main!(h) -> exit!(h Zero)";

/// Every program here and what each target makes of it, in the order
/// [`Target::ALL`] lists them: x86-64, wasm, and the 6502.
///
/// Ratchets: lower one when a target improves, and do not raise one without
/// saying why. These are the only thing that notices a decision a target
/// stops making, since a program answers the same either way.
fn corpus() -> Vec<(String, Program, [usize; 3])> {
    let built = built()
        .into_iter()
        .map(|(name, program, sizes)| (name.to_owned(), program, sizes));
    built.chain(written()).collect()
}

/// The programs this tier is handed, built rather than read.
#[expect(
    clippy::too_many_lines,
    reason = "one line per program; the length is the corpus"
)]
fn built() -> Vec<(&'static str, Program, [usize; 3])> {
    vec![
        ("empty", empty(), [127, 36, 30]),
        (
            "exit zero",
            faun::read(EXIT_ZERO).expect("a program"),
            [127, 36, 29],
        ),
        ("two and two", two_and_two(), [136, 105, 45]),
        ("hello world", faun::hello_world(), [158, 141, 63]),
        ("a call", calls_a_function(), [160, 125, 81]),
        ("recursion", recurses(), [245, 159, 232]),
        (
            "values across a call",
            values_survive_a_call(),
            [267, 204, 390],
        ),
        ("the heap", uses_the_heap(), [193, 137, 158]),
        ("a byte", stores_a_byte(), [241, 160, 215]),
        ("a global", counts_in_a_global(), [256, 158, 144]),
        ("writing the heap", writes_from_the_heap(), [206, 163, 177]),
        (
            "a computed length",
            writes_a_length_it_worked_out(),
            [225, 170, 190],
        ),
        ("eight bits", wraps_at_eight_bits(), [142, 118, 63]),
        ("less", less(7, 9), [143, 105, 63]),
        (
            "two worked out",
            compares_two_worked_out_values(),
            [170, 119, 89],
        ),
        ("a flag", branches_on_a_flag_it_read(), [257, 135, 119]),
        ("a countdown", countdown(3), [217, 173, 97]),
        (
            "a carried total",
            carries_a_total_into_an_arm(3),
            [281, 156, 103],
        ),
        (
            "a step first",
            counts_down_before_it_branches(3),
            [230, 172, 99],
        ),
        (
            "a long arm",
            a_branch_over_a_long_arm(40, true),
            [332, 401, 1008],
        ),
    ]
}

/// The examples, which are programs somebody wrote.
fn written() -> Vec<(String, Program, [usize; 3])> {
    [
        ("exit", [128, 96, 29]),
        ("two-and-two", [128, 96, 29]),
        ("double", [128, 96, 29]),
        ("leave", [141, 108, 49]),
        ("bool", [529, 296, 442]),
        ("nat", [1063, 554, 1242]),
        ("opaque", [152, 119, 76]),
        ("width", [278, 186, 212]),
    ]
    .into_iter()
    .map(|(name, sizes)| {
        let path = format!("examples/{name}.fn");
        let text = fs::read_to_string(&path).expect("an example");
        let program = faun::read(&text).unwrap_or_else(|e| panic!("{path}: {e}"));
        (path, program, sizes)
    })
    .collect()
}

#[test]
fn programs_compile_to_the_sizes_recorded_for_them() {
    for (name, program, sizes) in corpus() {
        for (target, size) in Target::ALL.into_iter().zip(sizes) {
            let bytes = faun::compile(target, &program)[0].bytes.len();
            assert_eq!(bytes, size, "{name} for {target}");
        }
    }
}

#[test]
fn every_target_adds_two_and_two() {
    for target in Target::ALL {
        assert_eq!(status(target, &two_and_two()), 4, "{target}");
    }
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_prints_hello_world() {
    let (output, _) = run(Target::X86_64Linux, &faun::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

#[test]
fn the_mos6502_image_prints_hello_world() {
    let (output, _) = run(Target::Mos6502Sim65, &faun::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

/// The branch that does not reach in one byte, which until now no program
/// here was long enough to need. Both targets that relax branches lay the
/// image out again with this one widened, and the answer is what says the
/// widened branch still lands where it meant to.
#[test]
fn every_target_branches_over_an_arm_a_byte_cannot_reach() {
    for target in Target::ALL {
        for first in [true, false] {
            let program = a_branch_over_a_long_arm(40, first);
            assert_eq!(
                status(target, &program),
                40,
                "{target}, long arm first: {first}"
            );
        }
    }
}

/// The shapes every target has an instruction for and no program here had
/// asked of it: both sides of a comparison worked out, a condition read
/// rather than just made, a routine's argument worked out, and a value
/// carried through a loop that only an arm reads.
#[test]
fn every_target_runs_what_a_constant_cannot_answer() {
    for target in Target::ALL {
        assert_eq!(
            status(target, &compares_two_worked_out_values()),
            1,
            "{target}"
        );
        assert_eq!(status(target, &branches_on_a_flag_it_read()), 7, "{target}");
        assert_eq!(
            run(target, &writes_a_length_it_worked_out()).0,
            "hi\n",
            "{target}"
        );
        assert_eq!(
            status(target, &carries_a_total_into_an_arm(3)),
            3,
            "{target}"
        );
        let ticks = counts_down_before_it_branches(3);
        assert_eq!(run(target, &ticks).0, "tick\n".repeat(3), "{target}");
    }
}

#[test]
fn every_target_counts_in_a_global() {
    for target in Target::ALL {
        assert_eq!(status(target, &counts_in_a_global()), 3, "{target}");
    }
}

#[test]
fn every_target_wraps_a_fixed_width() {
    for target in Target::ALL {
        assert_eq!(status(target, &wraps_at_eight_bits()), 4, "{target}");
    }
}

#[test]
fn the_mos6502_image_runs_every_program() {
    assert_eq!(status(Target::Mos6502Sim65, &empty()), 0);
    assert_eq!(status(Target::Mos6502Sim65, &less(7, 9)), 1);
    assert_eq!(status(Target::Mos6502Sim65, &less(9, 7)), 0);
    assert_eq!(status(Target::Mos6502Sim65, &calls_a_function()), 42);
    assert_eq!(status(Target::Mos6502Sim65, &recurses()), 6);
    assert_eq!(
        run(Target::Mos6502Sim65, &countdown(3)).0,
        "tick\n".repeat(3)
    );
    assert_eq!(status(Target::Mos6502Sim65, &uses_the_heap()), 42);
    assert_eq!(status(Target::Mos6502Sim65, &stores_a_byte()), 8);
    assert_eq!(run(Target::Mos6502Sim65, &writes_from_the_heap()).0, "hi\n");
    assert_eq!(status(Target::Mos6502Sim65, &values_survive_a_call()), 45);
}

#[test]
fn every_target_hands_back_what_a_call_would_destroy() {
    for target in Target::ALL {
        assert_eq!(status(target, &values_survive_a_call()), 45, "{target}");
    }
}

#[test]
fn every_target_writes_from_the_heap() {
    for target in Target::ALL {
        assert_eq!(run(target, &writes_from_the_heap()).0, "hi\n", "{target}");
    }
}

#[test]
fn the_wasm32_wasi_module_prints_hello_world() {
    let (output, _) = run(Target::Wasm32Wasi, &faun::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_smallest_x86_64_linux_executable_is_headers_and_an_exit() {
    // 120 bytes of header, then `push 60; pop rax; xor edi, edi; syscall`.
    let (output, _) = run(Target::X86_64Linux, &empty());
    assert_eq!(output, "");
}

#[test]
fn the_smallest_wasm32_wasi_module_imports_nothing() {
    // Type, function, export, code. No import section at all, no memory,
    // no data.
    let (output, _) = run(Target::Wasm32Wasi, &empty());
    assert_eq!(output, "");

    // A program that leaves with nought says so, and compiles to the same
    // module: `proc_exit(0)` is what running off the end of `_start` does.
    let written = faun::read(EXIT_ZERO).expect("a program");
    assert_eq!(
        faun::compile(Target::Wasm32Wasi, &written)[0].bytes,
        faun::compile(Target::Wasm32Wasi, &empty())[0].bytes
    );
}

/// Leaving with nought is a `return` only where returning ends the program.
/// A name that leaves is called, so it leaves through the routine wherever
/// it was called from.
#[test]
fn the_wasm32_wasi_module_imports_proc_exit_where_it_has_to() {
    let leaves = faun::read(
        "type Nat Zero Succ(Nat)

         leave!(h n) -> exit!(h n)

         main!(h) -> leave!(h Zero)",
    )
    .expect("a program");
    assert_eq!(status(Target::Wasm32Wasi, &leaves), 0);

    // Inside the entry, where one arm returns and the other has to call.
    assert_eq!(status(Target::Wasm32Wasi, &exits_from_a_branch(0)), 0);
    assert_eq!(status(Target::Wasm32Wasi, &exits_from_a_branch(1)), 5);
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_uses_the_heap() {
    assert_eq!(status(Target::X86_64Linux, &uses_the_heap()), 42);
    assert_eq!(status(Target::X86_64Linux, &stores_a_byte()), 8);
}

#[test]
fn the_wasm32_wasi_module_uses_the_heap() {
    assert_eq!(status(Target::Wasm32Wasi, &uses_the_heap()), 42);
    assert_eq!(status(Target::Wasm32Wasi, &stores_a_byte()), 8);
}

/// A call and a return, on each target's own calling convention.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_calls_a_function() {
    assert_eq!(status(Target::X86_64Linux, &calls_a_function()), 42);
    assert_eq!(status(Target::X86_64Linux, &recurses()), 6);
}

#[test]
fn the_wasm32_wasi_module_calls_a_function() {
    assert_eq!(status(Target::Wasm32Wasi, &calls_a_function()), 42);
    assert_eq!(status(Target::Wasm32Wasi, &recurses()), 6);
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_compares() {
    assert_eq!(status(Target::X86_64Linux, &less(7, 9)), 1);
    assert_eq!(status(Target::X86_64Linux, &less(9, 7)), 0);
}

#[test]
fn the_wasm32_wasi_module_compares() {
    assert_eq!(status(Target::Wasm32Wasi, &less(7, 9)), 1);
    assert_eq!(status(Target::Wasm32Wasi, &less(9, 7)), 0);
}

/// The IR's loop has to survive into both targets, which have nothing in
/// common about how they branch. Running it is the only proof that counts.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_counts_down() {
    assert_eq!(
        run(Target::X86_64Linux, &countdown(3)).0,
        "tick\n".repeat(3)
    );
    assert_eq!(run(Target::X86_64Linux, &countdown(0)).0, "");
}

#[test]
fn the_wasm32_wasi_module_counts_down() {
    assert_eq!(run(Target::Wasm32Wasi, &countdown(3)).0, "tick\n".repeat(3));
    assert_eq!(run(Target::Wasm32Wasi, &countdown(0)).0, "");
}

/// Two exits from one entry, one of them with nought. Whatever a target
/// makes of the second, the first has to leave with the status it says.
fn exits_from_a_branch(taken: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let exit = program.platform("exit");

    program.define(main, |b, _| {
        let value = b.constant(Word, taken);
        let zero = b.constant(Word, 0);
        let nought = b.compare(Relation::Equal, value, zero);
        b.if_(
            nought,
            &[],
            // Neither arm comes back, so neither reaches the join.
            |b| {
                let status = b.constant(Word, 0);
                b.platform_call(exit, &[status]);
                faun::ir::Terminator::UNREACHABLE
            },
            |b| {
                let status = b.constant(Word, 5);
                b.platform_call(exit, &[status]);
                faun::ir::Terminator::UNREACHABLE
            },
        );
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// An arm longer than a byte of displacement reaches over, which is the one
/// thing that makes a layout take more than a guess and a confirmation.
/// Which arm is long decides which branch cannot reach: the one jumping
/// over it to the join, or the one testing the condition.
///
/// The long arm is the arm that runs, so the answer is `steps` either way
/// and a branch landing anywhere else answers something else.
fn a_branch_over_a_long_arm(steps: u64, first: bool) -> Program {
    fn counts(b: &mut Builder, steps: u64) -> faun::ir::Terminator {
        let mut total = b.constant(Word, 0);
        for _ in 0..steps {
            let one = b.constant(Word, 1);
            total = b.binary(Binary::Add, total, one);
        }
        b.yield_(&[total])
    }
    fn nothing(b: &mut Builder) -> faun::ir::Terminator {
        let held = b.constant(Word, 0);
        b.yield_(&[held])
    }

    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        // Worked out rather than written, so no target folds the branch away
        // and lays the arms out as one run.
        let zero = b.constant(Word, 0);
        let held = b.constant(Word, u64::from(!first));
        let taken = b.compare(Relation::Equal, zero, held);
        let answer = if first {
            b.if_(taken, &[Word], |b| counts(b, steps), nothing)
        } else {
            b.if_(taken, &[Word], nothing, |b| counts(b, steps))
        };
        b.ret(&answer)
    });
    program
}

/// Both sides worked out, where every comparison here has had one side
/// written. A target with one accumulator has to hold the left somewhere
/// while it reads the right, and that is a different instruction.
fn compares_two_worked_out_values() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let one = b.constant(Word, 1);
        let two = b.binary(Binary::Add, one, one);
        let three = b.binary(Binary::Add, two, one);
        let answer = b.compare(Relation::Less, two, three);
        b.ret(&[answer])
    });
    program
}

/// A condition that is not the comparison just made: a flag read back out
/// of storage, which a target has to test for itself.
fn branches_on_a_flag_it_read() -> Program {
    let (mut program, main) = Program::new("main");
    let flag = program.global(&[1, 0, 0, 0, 0, 0, 0, 0]);

    program.define(main, |b, _| {
        let at = b.address_of(flag);
        let held = b.load(Width::Word, at, Offset::Words(0));
        let answer = b.if_(
            held,
            &[Word],
            |b| {
                let held = b.constant(Word, 7);
                b.yield_(&[held])
            },
            |b| {
                let held = b.constant(Word, 9);
                b.yield_(&[held])
            },
        );
        b.ret(&answer)
    });
    program
}

/// "hi\n" again, with the length worked out as well as the bytes, so
/// neither of the routine's arguments is a constant a target can lay down.
fn writes_a_length_it_worked_out() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");
    let write = program.platform("write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let one = b.constant(Word, 1);
        let two = b.constant(Word, 2);
        let length = b.binary(Binary::Add, one, two);
        b.platform_call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// A loop carrying a total that nothing in the body itself reads: both the
/// arm that leaves with it and the arm that adds to it are inside the `if`,
/// so whether it is still wanted is a question about the arms.
fn carries_a_total_into_an_arm(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        let total = b.constant(Word, 0);
        let answer = b.loop_(&[start, total], &[Word], |b, params| {
            let (n, total) = (params[0], params[1]);
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[total]),
                |b| {
                    let one = b.constant(Word, 1);
                    let next = b.binary(Binary::Sub, n, one);
                    let more = b.binary(Binary::Add, total, one);
                    b.continue_(&[next, more])
                },
            );
            faun::ir::Terminator::UNREACHABLE
        });
        b.ret(&answer)
    });
    program
}

/// The countdown again, with the step worked out in the body rather than in
/// the arm that goes round. Nothing in the body reads it -- the `if` sits
/// between the step and the `continue` carrying it -- so whether the step
/// may be left until last is a question about what the arms read.
fn counts_down_before_it_branches(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let tick = program.intern(b"tick\n".as_slice());
    let write = program.platform("write");

    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        b.loop_(&[start], &[], |b, params| {
            let n = params[0];
            let one = b.constant(Word, 1);
            let next = b.binary(Binary::Sub, n, one);
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[]),
                |b| {
                    let buf = b.address_of(tick);
                    let len = b.constant(Word, 5);
                    b.platform_call(write, &[buf, len]);
                    b.yield_(&[])
                },
            );
            b.continue_(&[next])
        });

        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// Nothing at all. A target's floor: headers, and whatever it takes to stop.
fn empty() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

fn two_and_two() -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let two = b.constant(Word, 2);
        let sum = b.binary(Binary::Add, two, two);
        b.ret(&[sum])
    });
    program
}

/// `main` calls `double(21)` and exits with it. The point is the call, so
/// the answer is the exit status rather than anything printed.
fn calls_a_function() -> Program {
    let (mut program, main) = Program::new("main");
    let double = program.declare("double", &[Word], &[Word]);
    program.define(double, |b, params| {
        let n = params[0];
        let doubled = b.binary(Binary::Add, n, n);
        b.ret(&[doubled])
    });

    program.define(main, |b, _| {
        let twenty_one = b.constant(Word, 21);
        let answer = b.call(double, &[twenty_one]);
        b.ret(&answer)
    });
    program
}

/// `sum(n)` recurses, so the call graph has a cycle and the callee needs a
/// frame that survives its own recursive call. 1 + 2 + 3 = 6.
fn recurses() -> Program {
    let (mut program, main) = Program::new("main");
    let sum = program.declare("sum", &[Word], &[Word]);
    program.define(sum, |b, params| {
        let n = params[0];
        let zero = b.constant(Word, 0);
        let done = b.compare(Relation::Equal, n, zero);
        let answer = b.if_(
            done,
            &[Word],
            |b| {
                let zero = b.constant(Word, 0);
                b.yield_(&[zero])
            },
            |b| {
                let one = b.constant(Word, 1);
                let less = b.binary(Binary::Sub, n, one);
                let rest = b.call(sum, &[less]);
                let total = b.binary(Binary::Add, n, rest[0]);
                b.yield_(&[total])
            },
        );
        b.ret(&answer)
    });

    program.define(main, |b, _| {
        let three = b.constant(Word, 3);
        let answer = b.call(sum, &[three]);
        b.ret(&answer)
    });
    program
}

/// Ask the platform for a page, write two words into it, read one back.
/// Exits with what it read, so nothing but real memory can make it pass.
fn uses_the_heap() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        let answer = b.constant(Word, 42);
        let decoy = b.constant(Word, 7);
        b.store(Width::Word, page, Offset::Words(0), decoy);
        b.store(Width::Word, page, Offset::Words(1), answer);

        let answer = b.load(Width::Word, page, Offset::Words(1));
        b.ret(&[answer])
    });
    program
}

/// Several values still wanted after a call, and a callee greedy enough to
/// take every pair it can. Anything the caller fails to hand back shows up
/// in the answer.
///
/// `clobber(x)` is `x + 2` through three intermediates; `outer(10, 3)` is
/// `13 + 7 + 12 + 10 + 3`.
fn values_survive_a_call() -> Program {
    let (mut program, main) = Program::new("main");
    let clobber = program.declare("clobber", &[Word], &[Word]);
    let outer = program.declare("outer", &[Word, Word], &[Word]);

    program.define(clobber, |b, params| {
        let x = params[0];
        let one = b.constant(Word, 1);
        let two = b.constant(Word, 2);
        let three = b.constant(Word, 3);
        let up = b.binary(Binary::Add, x, one);
        let down = b.binary(Binary::Sub, up, two);
        let back = b.binary(Binary::Add, down, three);
        b.ret(&[back])
    });

    program.define(outer, |b, params| {
        let (a, second) = (params[0], params[1]);
        let p = b.binary(Binary::Add, a, second);
        let q = b.binary(Binary::Sub, a, second);
        let r = b.call(clobber, &[a])[0];
        // Every one of these was computed before the call.
        let total = b.binary(Binary::Add, p, q);
        let total = b.binary(Binary::Add, total, r);
        let total = b.binary(Binary::Add, total, a);
        let total = b.binary(Binary::Add, total, second);
        b.ret(&[total])
    });

    program.define(main, |b, _| {
        let ten = b.constant(Word, 10);
        let three = b.constant(Word, 3);
        let answer = b.call(outer, &[ten, three]);
        b.ret(&answer)
    });
    program
}

/// Writes through an address the program worked out for itself, which is
/// the case a target cannot answer with a block of constants.
fn writes_from_the_heap() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");
    let write = program.platform("write");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        // "hi\n", a byte at a time, since the bytes are computed too.
        for (index, byte) in [b'h', b'i', b'\n'].into_iter().enumerate() {
            let value = b.constant(Word, u64::from(byte));
            let offset = Offset::Bytes(i32::try_from(index).expect("a short greeting"));
            b.store(Width::Byte, page, offset, value);
        }

        let length = b.constant(Word, 3);
        b.platform_call(write, &[page, length]);
        let status = b.constant(Word, 0);
        b.ret(&[status])
    });
    program
}

/// A byte store must not disturb its neighbour, and a byte above 127 must
/// come back zero-extended rather than as a very large word. Answers
/// `(first == 200) + second`, so both have to hold to reach 8.
fn stores_a_byte() -> Program {
    let (mut program, main) = Program::new("main");
    let grow = program.platform("grow");

    program.define(main, |b, _| {
        let size = b.constant(Word, 4096);
        let page = b.platform_call(grow, &[size])[0];

        let high = b.constant(Word, 200);
        b.store(Width::Byte, page, Offset::Bytes(0), high);
        let neighbour = b.constant(Word, 7);
        b.store(Width::Byte, page, Offset::Bytes(1), neighbour);

        let first = b.load(Width::Byte, page, Offset::Bytes(0));
        let second = b.load(Width::Byte, page, Offset::Bytes(1));
        let expected = b.constant(Word, 200);
        let intact = b.compare(Relation::Equal, first, expected);
        let answer = b.binary(Binary::Add, intact, second);
        b.ret(&[answer])
    });
    program
}

/// A counter in a writable datum, bumped by a function called three times.
/// Nothing but storage outliving a call can answer 3.
fn counts_in_a_global() -> Program {
    let (mut program, main) = Program::new("main");
    let counter = program.global(&[0; 8]);

    let bump = program.declare("bump", &[], &[]);
    program.define(bump, |b, _| {
        let at = b.address_of(counter);
        let seen = b.load(Width::Word, at, Offset::Words(0));
        let one = b.constant(Word, 1);
        let next = b.binary(Binary::Add, seen, one);
        b.store(Width::Word, at, Offset::Words(0), next);
        b.ret(&[])
    });

    program.define(main, |b, _| {
        b.call(bump, &[]);
        b.call(bump, &[]);
        b.call(bump, &[]);
        let at = b.address_of(counter);
        let answer = b.load(Width::Word, at, Offset::Words(0));
        b.ret(&[answer])
    });
    program
}

/// `Fixed { bits: 8 }` is arithmetic in Z/256, so 250 + 10 is 4 on every
/// target: free on a machine with eight-bit registers, a mask on the two
/// that are wider.
fn wraps_at_eight_bits() -> Program {
    let byte = Class::Fixed { bits: 8 };
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let left = b.constant(byte, 250);
        let right = b.constant(byte, 10);
        let sum = b.binary(Binary::Add, left, right);
        // The entry returns a word, and this is where the width changes.
        let answer = b.convert(Word, sum);
        b.ret(&[answer])
    });
    program
}

/// `Relation::Less` is unsigned, and both targets carry an arm for it that
/// nothing else exercises.
fn less(left: u64, right: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let left = b.constant(Word, left);
        let right = b.constant(Word, right);
        let answer = b.compare(Relation::Less, left, right);
        b.ret(&[answer])
    });
    program
}

/// `while n != 0 { print "tick"; n -= 1 }`, written the way the IR has it:
/// a loop carrying `n`, and an `if` that either breaks or goes round again.
fn countdown(times: u64) -> Program {
    let (mut program, main) = Program::new("main");
    let tick = program.intern(b"tick\n".as_slice());
    let write = program.platform("write");

    program.define(main, |b, _| {
        let start = b.constant(Word, times);
        b.loop_(&[start], &[], |b, params| {
            let n = params[0];
            let zero = b.constant(Word, 0);
            let done = b.compare(Relation::Equal, n, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[]),
                |b| {
                    let buf = b.address_of(tick);
                    let len = b.constant(Word, 5);
                    b.platform_call(write, &[buf, len]);
                    let one = b.constant(Word, 1);
                    let next = b.binary(Binary::Sub, n, one);
                    b.continue_(&[next])
                },
            );
            faun::ir::Terminator::UNREACHABLE
        });

        let status = b.constant(Word, 0);
        b.ret(&[status])
    });

    program
}

/// The exit status a program leaves with, which is what `main` returns.
/// WASI rejects anything outside `[0, 126)`, so a test that wants to check a
/// larger number has to reduce it to a small one first.
fn status(target: Target, program: &Program) -> i32 {
    execute(target, program).0
}

/// Compile, write, execute. Every program is validated first, since a class
/// disagreement is the kind of thing a target miscompiles in silence.
///
/// Returns what the program printed and how big it
/// was, so a test can pin both.
///
/// Serialised because the two halves race: another thread forking for its own
/// `Command` inherits this one's still-open write descriptor, and the exec
/// that follows fails with `ETXTBSY`.
fn run(target: Target, program: &Program) -> (String, usize) {
    let (code, output, size) = execute(target, program);
    assert_eq!(code, 0, "exited with {code}");
    (output, size)
}

fn execute(target: Target, program: &Program) -> (i32, String, usize) {
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    faun::ir::validate(program).expect("a well-formed program");
    target
        .accepts(program)
        .expect("a program this target holds");
    let _lock = ONE_AT_A_TIME.lock().unwrap_or_else(PoisonError::into_inner);

    let dir = std::env::temp_dir().join(format!(
        "faun-{}-{:?}-{}",
        std::process::id(),
        target,
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir_all(&dir).unwrap();
    let path = write(target, &dir.join("program"), program);

    let output = match target {
        Target::X86_64Linux => Command::new(&path).output().unwrap(),
        Target::Wasm32Wasi => Command::new("wasmtime").arg(&path).output().unwrap(),
        Target::Mos6502Sim65 => Command::new("sim65").arg(&path).output().unwrap(),
    };
    let size = usize::try_from(fs::metadata(&path).unwrap().len()).unwrap();
    fs::remove_dir_all(&dir).unwrap();

    let code = output.status.code().expect("the program was not signalled");
    (code, String::from_utf8(output.stdout).unwrap(), size)
}

fn write(target: Target, output: &Path, program: &Program) -> PathBuf {
    let artifacts = faun::compile(target, program);
    assert_eq!(artifacts.len(), 1);

    let mut path = output.to_path_buf().into_os_string();
    path.push(artifacts[0].extension);
    let path = PathBuf::from(path);
    fs::write(&path, &artifacts[0].bytes).unwrap();

    #[cfg(unix)]
    if artifacts[0].executable {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    }

    path
}

/// The whole way down: `2 + 2` written in barb, lowered through the machine
/// tier, compiled, and run. `Nat` is inductive all the way to the lowering,
/// which is where it becomes a word.
#[test]
fn every_target_runs_two_and_two_from_barb() {
    let barb = faun::two_and_two();
    let facts = faun::barb::recognise(&barb);
    let machine = faun::ir::lower(&barb, &facts).expect("a representable program");

    // `add` was recognised, so it is an instruction rather than a function:
    // what is left is the entry alone.
    assert_eq!(machine.functions().len(), 1, "only the entry survives");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 4, "{target}");
    }
}

/// The same program again, written out rather than built, and run.
#[test]
fn every_target_runs_two_and_two_from_text() {
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) -> exit!(h add(Succ(Succ(Zero)) Succ(Succ(Zero))))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 4, "{target}");
    }
}

/// Every example compiles and answers what it says it does, so that one
/// cannot rot into a program that no longer reads.
#[test]
fn every_target_runs_every_example() {
    for entry in fs::read_dir("examples").expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let machine = faun::read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        for target in Target::ALL {
            assert_eq!(
                status(target, &machine),
                4,
                "{} on {target}",
                path.display()
            );
        }
    }
}

/// The one effect there is: a program that leaves with a status it worked
/// out, through a platform routine it declared and a host it was handed.
#[test]
fn every_target_exits_with_what_it_was_told() {
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         main!(h) -> exit!(h Succ(Succ(Succ(Zero))))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 3, "{target}");
    }
}

/// However many calls deep it is, a name that leaves does not come back: the
/// status is the one it was handed, and nothing after the call is reached.
#[test]
fn every_target_exits_through_a_name_that_leaves() {
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         die!(h n) -> exit!(h n)

         main!(h) -> die!(h Succ(Succ(Zero)))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 2, "{target}");
    }
}

/// A clause that leaves is one the others are not measured against, so a
/// name with an arm that exits still answers what its other arm answers.
#[test]
fn every_target_runs_a_match_with_an_arm_that_leaves() {
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         pick!(h Zero) -> exit!(h Succ(Zero))
         pick!(h Succ(k)) -> k

         main!(h) -> exit!(h Succ(pick!(h Succ(Succ(Zero)))))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 2, "{target}");
    }

    // The other way through, which leaves from inside the match.
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         pick!(h Zero) -> exit!(h Succ(Zero))
         pick!(h Succ(k)) -> k

         main!(h) -> exit!(h Succ(pick!(h Zero)))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 1, "{target}");
    }
}

/// What a routine reads is what the name means, not what a program hands
/// it. A type with one constructor says nothing by being one value rather
/// than another, so it carries no bits and is not passed at all -- which
/// leaves `exit!` with no status to leave with.
#[test]
fn an_effect_hands_over_what_the_routine_reads() {
    let refused = faun::read(
        "type Nat Zero

         main!(h) -> exit!(h Zero)",
    )
    .unwrap_err();
    assert!(
        refused.contains("`exit!` hands over nothing, but `exit` reads a word"),
        "{refused}"
    );
}

/// A pure name may not do observable work.
#[test]
fn a_pure_name_cannot_call_an_effect() {
    let refused = faun::read(
        "type Nat Zero Succ(Nat)

         quietly(h) -> exit!(h Zero)

         main!(h) -> quietly(h)",
    )
    .unwrap_err();
    assert!(
        refused.contains("`quietly` is pure and calls `exit!`"),
        "{refused}"
    );
}

/// A type whose constructors carry nothing is a tag, and matching one asks
/// which it is. Three of them, so the asking is a run of tests rather than
/// the single question a number's two constructors answer.
#[test]
fn every_target_reads_a_tag() {
    let ordering = "type Nat Zero Succ(Nat)
                    type Order Lt Eq Gt

                    rank(Lt) -> Zero
                    rank(Eq) -> Succ(Zero)
                    rank(Gt) -> Succ(Succ(Zero))

                    pick(Zero) -> Lt
                    pick(Succ(k)) -> Gt

                    main!(h) -> exit!(h rank(pick(WHICH)))";

    for (which, answer) in [("Zero", 0), ("Succ(Zero)", 2)] {
        let machine = faun::read(&ordering.replace("WHICH", which)).expect("a program");
        for target in Target::ALL {
            assert_eq!(status(target, &machine), answer, "{which} on {target}");
        }
    }
}

/// A tag is which constructor it is, and a number is what it counts to.
/// Writing `Succ` before `Zero` moves the tags and must not move either.
#[test]
fn every_target_tells_a_tag_from_a_count() {
    let machine = faun::read(
        "type Nat Succ(Nat) Zero
         type Bool True False

         count(False) -> Zero
         count(True) -> Succ(Zero)

         main!(h) -> exit!(h count(True))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 1, "{target}");
    }
}

/// What a tag is not: a constructor carrying something has no
/// representation here yet, however many of them there are.
#[test]
fn a_constructor_that_carries_something_is_not_a_tag() {
    let refused = faun::read(
        "type Nat Zero Succ(Nat)
         type Maybe None Some(Nat)

         main!(h) -> exit!(h Zero)",
    )
    .unwrap_err();
    assert!(
        refused.contains("`Maybe` has no representation"),
        "{refused}"
    );
}

/// A clause matches as many arguments as it likes, which is what `sub` and
/// `cmp` want: both take two numbers apart at once. What that compiles to
/// is a match per column, so the answer is the only thing that says the
/// rows were narrowed in the right order.
#[test]
fn every_target_matches_on_more_than_one_argument() {
    let arithmetic = "type Nat Zero Succ(Nat)
                      type Order Lt Eq Gt

                      sub(Zero b) -> Zero
                      sub(Succ(m) Zero) -> Succ(m)
                      sub(Succ(m) Succ(n)) -> sub(m n)

                      cmp(Zero Zero) -> Eq
                      cmp(Zero Succ(n)) -> Lt
                      cmp(Succ(m) Zero) -> Gt
                      cmp(Succ(m) Succ(n)) -> cmp(m n)

                      rank(Lt) -> Zero
                      rank(Eq) -> Succ(Zero)
                      rank(Gt) -> Succ(Succ(Zero))

                      three(n) -> Succ(Succ(Succ(n)))

                      main!(h) -> exit!(h ANSWER)";

    // Subtraction stops at nought rather than wrapping, which is the whole
    // of what the second column buys: the arm for `Succ(m) Zero` is the one
    // that says so.
    for (answer, want) in [
        ("sub(three(Zero) Succ(Zero))", 2),
        ("sub(Succ(Zero) three(Zero))", 0),
        ("rank(cmp(Succ(Zero) three(Zero)))", 0),
        ("rank(cmp(three(Zero) three(Zero)))", 1),
        ("rank(cmp(three(Zero) Succ(Zero)))", 2),
    ] {
        let machine = faun::read(&arithmetic.replace("ANSWER", answer)).expect("a program");
        for target in Target::ALL {
            assert_eq!(status(target, &machine), want, "{answer} on {target}");
        }
    }
}

/// A program is what runs from its entry. A name nothing reaches is not
/// part of it, however much of it there is.
#[test]
fn what_nothing_reaches_is_not_emitted() {
    let reached = "type Nat Zero Succ(Nat)

                   double(n) -> add(n n)
                   add(a Zero) -> a
                   add(a Succ(k)) -> Succ(add(a k))

                   main!(h) -> exit!(h double(Succ(Succ(Zero))))";
    let spare = format!(
        "{reached}

         quadruple(n) -> double(double(n))
         quadruple_again(n) -> quadruple(quadruple(n))"
    );

    for target in Target::ALL {
        let machine = faun::read(reached).expect("a program");
        let spare = faun::read(&spare).expect("a program");
        assert_eq!(status(target, &machine), 4, "{target}");
        assert_eq!(
            faun::compile(target, &spare)[0].bytes,
            faun::compile(target, &machine)[0].bytes,
            "{target}"
        );
    }
}

/// A chain of constructors is the number it builds, read back here rather
/// than built an instruction at a time. So a longer chain is not a longer
/// program, and the answer is what says it was read back rightly.
#[test]
fn a_chain_of_constructors_is_the_number_it_builds() {
    let chain = |held: usize| {
        let text = format!(
            "type Nat Zero Succ(Nat)\n\nmain!(h) -> exit!(h {}Zero{})",
            "Succ(".repeat(held),
            ")".repeat(held)
        );
        faun::read(&text).expect("a program")
    };

    for target in Target::ALL {
        assert_eq!(status(target, &chain(4)), 4, "{target}");
        assert_eq!(status(target, &chain(40)), 40, "{target}");
        assert_eq!(
            faun::compile(target, &chain(40))[0].bytes.len(),
            faun::compile(target, &chain(4))[0].bytes.len(),
            "{target}"
        );
    }
}

/// What a program works out before it runs is not something a target sees.
/// A program of constants is the constant it answers, and one it was handed
/// a value for is the work it was written as.
#[test]
fn what_is_known_is_worked_out_before_a_target_sees_it() {
    let arithmetic = "type Nat Zero Succ(Nat)

                      add(a Zero) -> a
                      add(a Succ(k)) -> Succ(add(a k))

                      mul(Zero b) -> Zero
                      mul(Succ(k) b) -> add(b mul(k b))

                      main!(h) ->
                        two = HELD
                        exit!(h mul(two two))";
    let known = faun::read(&arithmetic.replace("HELD", "Succ(Succ(Zero))")).expect("a program");
    let handed =
        faun::read(&arithmetic.replace("HELD", "opaque!(h Succ(Succ(Zero)))")).expect("a program");
    let four = faun::read(
        "type Nat Zero Succ(Nat)

         main!(h) -> exit!(h Succ(Succ(Succ(Succ(Zero)))))",
    )
    .expect("a program");

    for target in Target::ALL {
        assert_eq!(status(target, &known), 4, "{target}");
        assert_eq!(status(target, &handed), 4, "{target}");

        // Nothing is left of the multiplication, nor of anything it called.
        assert_eq!(
            faun::compile(target, &known)[0].bytes,
            faun::compile(target, &four)[0].bytes,
            "{target}"
        );
        // And everything is left of it where the value was handed over.
        let handed = faun::compile(target, &handed)[0].bytes.len();
        assert!(
            handed > faun::compile(target, &four)[0].bytes.len(),
            "{target}"
        );
    }
}

/// A definition may go round only on something it took apart, so each time
/// round is over something smaller and the taking apart has an end. Which
/// is what lets the tier above work a term out without wondering whether it
/// will come back.
#[test]
fn a_definition_that_does_not_stop_is_refused() {
    let refused = faun::read(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         spin(n) -> add(Zero spin(n))

         main!(h) -> exit!(h spin(Zero))",
    )
    .unwrap_err();
    assert!(
        refused.contains("nothing here shows `spin` stops"),
        "{refused}"
    );

    // The same shape, taking its argument apart: this one has an end.
    let machine = faun::read(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         twice(Zero) -> Zero
         twice(Succ(k)) -> Succ(Succ(twice(k)))

         main!(h) ->
           two = opaque!(h Succ(Succ(Zero)))
           exit!(h twice(two))",
    )
    .expect("a program");
    for target in Target::ALL {
        assert_eq!(status(target, &machine), 4, "{target}");
    }
}

/// A word is as wide as the machine is, so a number whose size a program
/// knows is a claim about which machines will run it. Nothing above the
/// targets can check that claim, because a class saying `Word` means
/// something different on each of them.
#[test]
fn a_target_says_what_it_cannot_hold() {
    let big = |held: u64| {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            let held = b.constant(Word, held);
            b.ret(&[held])
        });
        program
    };

    // Seventy thousand needs seventeen bits, which the 6502 does not have.
    let program = big(70_000);
    assert!(Target::X86_64Linux.accepts(&program).is_ok());
    assert!(Target::Wasm32Wasi.accepts(&program).is_ok());
    let refused = Target::Mos6502Sim65.accepts(&program).unwrap_err();
    assert!(refused.contains("holds 16 bits, and 70000"), "{refused}");

    // And what every target holds, every target holds.
    let program = big(4);
    for target in Target::ALL {
        assert!(target.accepts(&program).is_ok(), "{target}");
    }

    // A value needing more bits than a target holds is the same refusal.
    // Narrower than its word is not: what a value holds above the bits it
    // needs is nought, so a target holds it in whatever it has.
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let held = b.constant(Class::Fixed { bits: 32 }, 1);
        b.ret(&[held])
    });
    assert!(Target::X86_64Linux.accepts(&program).is_ok());
    assert!(Target::Wasm32Wasi.accepts(&program).is_ok());
    let refused = Target::Mos6502Sim65.accepts(&program).unwrap_err();
    assert!(
        refused.contains("holds 16 bits, and a value here needs 32"),
        "{refused}"
    );
}

/// How wide a number is held is what its values can be, worked out by the
/// tier above from what the program does with them. Nothing says it and
/// nothing wraps: a value needing three bits is held in three bits, and a
/// value nothing bounds is held in a machine word.
#[test]
fn how_wide_a_number_is_held_is_what_it_can_be() {
    let widths = |text: &str| {
        let program = faun::read(text).expect("a program");
        (0..program.values_count())
            .map(|at| program.class(faun::ir::ValueId::at(at)))
            .collect::<Vec<_>>()
    };

    // Two and two is four, which three bits hold.
    let held = widths(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) ->
           two = opaque!(h Succ(Succ(Zero)))
           exit!(h add(two two))",
    );
    assert!(held.contains(&Class::Fixed { bits: 3 }), "{held:?}");
    assert!(
        held.iter()
            .all(|held| held.fits(Class::Fixed { bits: 3 }) || *held == Word),
        "{held:?}"
    );

    // Counting up without a last step has no last value, and then there is
    // nothing to say but a machine word.
    let held = widths(
        "type Nat Zero Succ(Nat)

         up(Zero) -> Succ(Zero)
         up(Succ(k)) -> Succ(Succ(up(k)))

         main!(h) ->
           n = opaque!(h Succ(Zero))
           exit!(h up(n))",
    );
    // Nought is nought however wide the numbers around it are; what says
    // this one is unbounded is that nothing in it is held narrower than a
    // word except the constants that cannot be anything else.
    assert!(held.contains(&Word), "{held:?}");
    assert!(
        !held
            .iter()
            .any(|held| matches!(*held, Class::Fixed { bits } if bits > 1)),
        "{held:?}"
    );
}
