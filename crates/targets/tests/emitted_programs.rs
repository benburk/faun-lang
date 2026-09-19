//! Compile for each target, then actually run the result.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, PoisonError};

use faun::ir::Class::Word;
use faun::ir::{Class, Program};
use faun::programs;
use faun::targets::Target;

/// Read against what a compiler knows, since nothing here is about a
/// routine somebody wrote down.
fn read(text: &str) -> Result<Program, String> {
    faun::read(text, &faun::platform::Routines::builtin())
}

use faun_mos6502_sim65::Mos6502Sim65;
use faun_targets::ALL;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

/// The whole of a program that does nothing: a number to leave with, and the
/// one effect there is. This is the floor for a program somebody writes,
/// where [`empty`] is the floor for one this tier is handed.
const EXIT_ZERO: &str = "type Nat Zero Succ(Nat)

                         main!(h) -> exit!(h Zero)";

/// Every program here and what each target makes of it, in the order
/// [`ALL`] lists them: x86-64, wasm, and the 6502.
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
        ("empty", programs::empty(), [127, 36, 30]),
        (
            "exit zero",
            read(EXIT_ZERO).expect("a program"),
            [127, 36, 29],
        ),
        ("two and two", programs::two_and_two(), [136, 105, 45]),
        ("hello world", programs::hello_world(), [158, 141, 63]),
        ("a call", programs::calls_a_function(), [160, 125, 81]),
        ("recursion", programs::recurses(), [245, 159, 232]),
        (
            "values across a call",
            programs::values_survive_a_call(),
            [267, 204, 390],
        ),
        ("the heap", programs::uses_the_heap(), [193, 137, 158]),
        ("a byte", programs::stores_a_byte(), [241, 160, 215]),
        ("a global", programs::counts_in_a_global(), [256, 158, 144]),
        (
            "writing the heap",
            programs::writes_from_the_heap(),
            [206, 163, 177],
        ),
        (
            "a computed length",
            programs::writes_a_length_it_worked_out(),
            [225, 170, 190],
        ),
        (
            "eight bits",
            programs::wraps_at_eight_bits(),
            [142, 118, 63],
        ),
        ("less", programs::less(7, 9), [143, 105, 63]),
        (
            "two worked out",
            programs::compares_two_worked_out_values(),
            [170, 119, 89],
        ),
        (
            "a flag",
            programs::branches_on_a_flag_it_read(),
            [257, 135, 119],
        ),
        ("a countdown", programs::countdown(3), [217, 173, 97]),
        (
            "a carried total",
            programs::carries_a_total_into_an_arm(3),
            [281, 156, 103],
        ),
        (
            "a step first",
            programs::counts_down_before_it_branches(3),
            [230, 172, 99],
        ),
        (
            "a long arm",
            programs::a_branch_over_a_long_arm(40, true),
            [332, 401, 1008],
        ),
    ]
}

/// Where the examples are. They belong to the project rather than to any one
/// crate, so they are not found by where a test happens to be run from.
fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// The examples, which are programs somebody wrote.
fn written() -> Vec<(String, Program, [usize; 3])> {
    [
        ("exit", [128, 96, 29]),
        ("two-and-two", [128, 96, 29]),
        ("double", [128, 96, 29]),
        ("leave", [141, 108, 49]),
        ("bool", [628, 390, 533]),
        ("nat", [1087, 604, 1265]),
        ("width", [294, 239, 225]),
        ("argc", [187, 179, 102]),
    ]
    .into_iter()
    .map(|(name, sizes)| {
        let path = examples().join(format!("{name}.fn"));
        let text = fs::read_to_string(&path).expect("an example");
        let program = read(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
        (name.to_owned(), program, sizes)
    })
    .collect()
}

#[test]
fn programs_compile_to_the_sizes_recorded_for_them() {
    for (name, program, sizes) in corpus() {
        for (target, size) in ALL.into_iter().zip(sizes) {
            let bytes = target.emit(&program)[0].bytes.len();
            assert_eq!(bytes, size, "{name} for {target}");
        }
    }
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_prints_hello_world() {
    let (output, _) = run(&X86_64Linux, &programs::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

#[test]
fn the_mos6502_image_prints_hello_world() {
    let (output, _) = run(&Mos6502Sim65, &programs::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

#[test]
fn the_mos6502_image_runs_every_program() {
    assert_eq!(status(&Mos6502Sim65, &programs::empty()), 0);
    assert_eq!(status(&Mos6502Sim65, &programs::less(7, 9)), 1);
    assert_eq!(status(&Mos6502Sim65, &programs::less(9, 7)), 0);
    assert_eq!(status(&Mos6502Sim65, &programs::calls_a_function()), 42);
    assert_eq!(status(&Mos6502Sim65, &programs::recurses()), 6);
    assert_eq!(
        run(&Mos6502Sim65, &programs::countdown(3)).0,
        "tick\n".repeat(3)
    );
    assert_eq!(status(&Mos6502Sim65, &programs::uses_the_heap()), 42);
    assert_eq!(status(&Mos6502Sim65, &programs::stores_a_byte()), 8);
    assert_eq!(
        run(&Mos6502Sim65, &programs::writes_from_the_heap()).0,
        "hi\n"
    );
    assert_eq!(
        status(&Mos6502Sim65, &programs::values_survive_a_call()),
        45
    );
}

#[test]
fn the_wasm32_wasi_module_prints_hello_world() {
    let (output, _) = run(&Wasm32Wasi, &programs::hello_world());
    assert_eq!(output, "Hello, World!\n");
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_smallest_x86_64_linux_executable_is_headers_and_an_exit() {
    // 120 bytes of header, then `push 60; pop rax; xor edi, edi; syscall`.
    let (output, _) = run(&X86_64Linux, &programs::empty());
    assert_eq!(output, "");
}

#[test]
fn the_smallest_wasm32_wasi_module_imports_nothing() {
    // Type, function, export, code. No import section at all, no memory,
    // no data.
    let (output, _) = run(&Wasm32Wasi, &programs::empty());
    assert_eq!(output, "");

    // A program that leaves with nought says so, and compiles to the same
    // module: `proc_exit(0)` is what running off the end of `_start` does.
    let written = read(EXIT_ZERO).expect("a program");
    assert_eq!(
        Wasm32Wasi.emit(&written)[0].bytes,
        Wasm32Wasi.emit(&programs::empty())[0].bytes
    );
}

/// Leaving with nought is a `return` only where returning ends the program.
/// A name that leaves is called, so it leaves through the routine wherever
/// it was called from.
#[test]
fn the_wasm32_wasi_module_imports_proc_exit_where_it_has_to() {
    let leaves = read(
        "type Nat Zero Succ(Nat)

         leave!(h n) -> exit!(h n)

         main!(h) -> leave!(h Zero)",
    )
    .expect("a program");
    assert_eq!(status(&Wasm32Wasi, &leaves), 0);

    // Inside the entry, where one arm returns and the other has to call.
    assert_eq!(status(&Wasm32Wasi, &programs::exits_from_a_branch(0)), 0);
    assert_eq!(status(&Wasm32Wasi, &programs::exits_from_a_branch(1)), 5);
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_uses_the_heap() {
    assert_eq!(status(&X86_64Linux, &programs::uses_the_heap()), 42);
    assert_eq!(status(&X86_64Linux, &programs::stores_a_byte()), 8);
}

#[test]
fn the_wasm32_wasi_module_uses_the_heap() {
    assert_eq!(status(&Wasm32Wasi, &programs::uses_the_heap()), 42);
    assert_eq!(status(&Wasm32Wasi, &programs::stores_a_byte()), 8);
}

/// A call and a return, on each target's own calling convention.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_calls_a_function() {
    assert_eq!(status(&X86_64Linux, &programs::calls_a_function()), 42);
    assert_eq!(status(&X86_64Linux, &programs::recurses()), 6);
}

#[test]
fn the_wasm32_wasi_module_calls_a_function() {
    assert_eq!(status(&Wasm32Wasi, &programs::calls_a_function()), 42);
    assert_eq!(status(&Wasm32Wasi, &programs::recurses()), 6);
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_compares() {
    assert_eq!(status(&X86_64Linux, &programs::less(7, 9)), 1);
    assert_eq!(status(&X86_64Linux, &programs::less(9, 7)), 0);
}

#[test]
fn the_wasm32_wasi_module_compares() {
    assert_eq!(status(&Wasm32Wasi, &programs::less(7, 9)), 1);
    assert_eq!(status(&Wasm32Wasi, &programs::less(9, 7)), 0);
}

/// The IR's loop has to survive into both targets, which have nothing in
/// common about how they branch. Running it is the only proof that counts.
#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn the_x86_64_linux_executable_counts_down() {
    assert_eq!(
        run(&X86_64Linux, &programs::countdown(3)).0,
        "tick\n".repeat(3)
    );
    assert_eq!(run(&X86_64Linux, &programs::countdown(0)).0, "");
}

#[test]
fn the_wasm32_wasi_module_counts_down() {
    assert_eq!(
        run(&Wasm32Wasi, &programs::countdown(3)).0,
        "tick\n".repeat(3)
    );
    assert_eq!(run(&Wasm32Wasi, &programs::countdown(0)).0, "");
}

/// The exit status a program leaves with, which is what `main` returns.
/// WASI rejects anything outside `[0, 126)`, so a test that wants to check a
/// larger number has to reduce it to a small one first.
fn status(target: &dyn Target, program: &Program) -> i32 {
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
fn run(target: &dyn Target, program: &Program) -> (String, usize) {
    let (code, output, size) = execute(target, program);
    assert_eq!(code, 0, "exited with {code}");
    (output, size)
}

fn execute(target: &dyn Target, program: &Program) -> (i32, String, usize) {
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

    // How a machine that is not this one is run, which is a fact about the
    // tools here rather than about the target.
    let output = match target.name() {
        "x86_64-linux" => Command::new(&path).output().unwrap(),
        "wasm32-wasi" => Command::new("wasmtime").arg(&path).output().unwrap(),
        "mos6502-sim65" => Command::new("sim65").arg(&path).output().unwrap(),
        held => panic!("nothing here runs {held}"),
    };
    let size = usize::try_from(fs::metadata(&path).unwrap().len()).unwrap();
    fs::remove_dir_all(&dir).unwrap();

    let code = output.status.code().expect("the program was not signalled");
    (code, String::from_utf8(output.stdout).unwrap(), size)
}

fn write(target: &dyn Target, output: &Path, program: &Program) -> PathBuf {
    let artifacts = target.emit(program);
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
    let barb = programs::two_and_two_in_barb();
    let facts = faun::barb::recognise(&barb);
    let machine = faun::ir::lower(&barb, &facts, &faun::platform::Routines::builtin())
        .expect("a representable program");

    // `add` was recognised, so it is an instruction rather than a function:
    // what is left is the entry alone.
    assert_eq!(machine.functions().len(), 1, "only the entry survives");
    for target in ALL {
        assert_eq!(status(target, &machine), 4, "{target}");
    }
}

/// Every example compiles and answers what it says it does, so that one
/// cannot rot into a program that no longer reads.
#[test]
fn every_target_runs_every_example() {
    for entry in fs::read_dir(examples()).expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let machine = read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        for target in ALL {
            assert_eq!(
                status(target, &machine),
                4,
                "{} on {target}",
                path.display()
            );
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

    for target in ALL {
        let machine = read(reached).expect("a program");
        let spare = read(&spare).expect("a program");
        assert_eq!(status(target, &machine), 4, "{target}");
        assert_eq!(
            target.emit(&spare)[0].bytes,
            target.emit(&machine)[0].bytes,
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
        read(&text).expect("a program")
    };

    for target in ALL {
        assert_eq!(status(target, &chain(4)), 4, "{target}");
        assert_eq!(status(target, &chain(40)), 40, "{target}");
        assert_eq!(
            target.emit(&chain(40))[0].bytes.len(),
            target.emit(&chain(4))[0].bytes.len(),
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
    let known = read(&arithmetic.replace("HELD", "Succ(Succ(Zero))")).expect("a program");
    let four = read(
        "type Nat Zero Succ(Nat)

         main!(h) -> exit!(h Succ(Succ(Succ(Succ(Zero)))))",
    )
    .expect("a program");

    for target in ALL {
        assert_eq!(status(target, &known), 4, "{target}");

        // Nothing is left of the multiplication, nor of anything it called.
        assert_eq!(
            target.emit(&known)[0].bytes,
            target.emit(&four)[0].bytes,
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
    let refused = read(
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
    let machine = read(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         twice(Zero) -> Zero
         twice(Succ(k)) -> Succ(Succ(twice(k)))

         main!(h) ->
           two = Succ(Succ(Zero))
           exit!(h twice(two))",
    )
    .expect("a program");
    for target in ALL {
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
    assert!(&X86_64Linux.accepts(&program).is_ok());
    assert!(&Wasm32Wasi.accepts(&program).is_ok());
    let refused = &Mos6502Sim65.accepts(&program).unwrap_err();
    assert!(refused.contains("holds 16 bits, and 70000"), "{refused}");

    // And what every target holds, every target holds.
    let program = big(4);
    for target in ALL {
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
    assert!(&X86_64Linux.accepts(&program).is_ok());
    assert!(&Wasm32Wasi.accepts(&program).is_ok());
    let refused = &Mos6502Sim65.accepts(&program).unwrap_err();
    assert!(
        refused.contains("holds 16 bits, and a value here needs 32"),
        "{refused}"
    );
}

/// What a target says it answers for is what something answers for it.
///
/// The name is how a routine is reached, so one spelled wrong here is a
/// program refused for naming something that exists, or a backend reached
/// by a name its own `match` has no arm for. Neither says what went wrong.
#[test]
fn every_target_provides_routines_that_exist() {
    for target in ALL {
        for held in target.provides() {
            assert!(
                faun::platform::Routines::builtin().get(held).is_some(),
                "{target} answers for `{held}`, which is not a routine"
            );
        }
    }
}

/// Every target answers what every program says, and the same as every
/// other. What a program answers is a fact about the program, so this asks
/// each machine the same question rather than a different one per machine.
#[test]
fn every_target_answers_what_a_program_says() {
    for (name, program, answer) in programs::running() {
        for target in ALL {
            assert_eq!(status(target, &program), answer, "{name} on {target}");
        }
    }
}

/// And the same of what one writes.
#[test]
fn every_target_writes_what_a_program_writes() {
    for (name, program, written) in programs::printing() {
        for target in ALL {
            assert_eq!(run(target, &program).0, written, "{name} on {target}");
        }
    }
}
