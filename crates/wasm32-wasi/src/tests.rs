//! What this machine makes of the programs every machine is handed.
//!
//! What a program answers is `faun::programs`' to say, since it is the same
//! answer on every machine. What one costs in bytes is this one's, because
//! no two lay the same program out the same way.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, PoisonError};

use faun::ir::{Class, Program};
use faun::programs;
use faun::targets::Target;

use crate::Wasm32Wasi;

/// The whole of a program that does nothing: a number to leave with, and
/// the one effect there is.
const EXIT_ZERO: &str = "type Nat Zero Succ(Nat)

                         main!(h) -> exit!(h Zero)";

/// Every program built here and what this machine compiles it to.
///
/// Ratchets: lower one when this target improves, and do not raise one
/// without saying why. These are the only thing that notices a decision
/// this target stops making, since a program answers the same either way.
#[expect(clippy::too_many_lines, reason = "a table of programs")]
fn corpus() -> Vec<(&'static str, Program, usize)> {
    vec![
        ("empty", programs::empty(), 36),
        ("exit zero", read(EXIT_ZERO).expect("a program"), 36),
        ("two and two", programs::two_and_two(), 105),
        ("hello world", programs::hello_world(), 141),
        ("a call", programs::calls_a_function(), 125),
        ("recursion", programs::recurses(), 159),
        (
            "values across a call",
            programs::values_survive_a_call(),
            204,
        ),
        ("the heap", programs::uses_the_heap(), 137),
        ("a byte", programs::stores_a_byte(), 160),
        ("a global", programs::counts_in_a_global(), 158),
        ("writing the heap", programs::writes_from_the_heap(), 163),
        (
            "a computed length",
            programs::writes_a_length_it_worked_out(),
            170,
        ),
        ("eight bits", programs::wraps_at_eight_bits(), 118),
        ("less", programs::less(7, 9), 105),
        (
            "two worked out",
            programs::compares_two_worked_out_values(),
            119,
        ),
        ("a flag", programs::branches_on_a_flag_it_read(), 135),
        ("a countdown", programs::countdown(3), 173),
        (
            "a carried total",
            programs::carries_a_total_into_an_arm(3),
            156,
        ),
        (
            "a step first",
            programs::counts_down_before_it_branches(3),
            172,
        ),
        (
            "a long arm",
            programs::a_branch_over_a_long_arm(40, true),
            401,
        ),
    ]
}

/// And the same of the examples, which are programs somebody wrote.
fn examples() -> Vec<(String, Program, usize)> {
    [
        ("exit", 96),
        ("two-and-two", 96),
        ("double", 96),
        ("leave", 108),
        ("bool", 390),
        ("nat", 604),
        ("width", 239),
        ("argc", 179),
    ]
    .into_iter()
    .map(|(name, size)| {
        let path = written().join(format!("{name}.fn"));
        let text = fs::read_to_string(&path).expect("an example");
        let program = read(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
        (name.to_owned(), program, size)
    })
    .collect()
}

/// Where the examples are. They belong to the project rather than to any
/// one crate, so they are not found by where a test happens to be run from.
fn written() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// A program read from text, against what this machine answers for.
fn read(text: &str) -> Result<Program, String> {
    faun::read(text, &Wasm32Wasi.routines())
}

/// Write it out, run it, and say what it left with, what it wrote, and what
/// it cost.
fn execute(program: &Program) -> (i32, String, usize) {
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    faun::ir::validate(program).expect("a well-formed program");
    Wasm32Wasi
        .accepts(program)
        .expect("a program this machine holds");
    let _lock = ONE_AT_A_TIME.lock().unwrap_or_else(PoisonError::into_inner);

    let dir = std::env::temp_dir().join(format!(
        "faun-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("a clock after the epoch")
            .as_nanos()
    ));
    fs::create_dir_all(&dir).expect("a scratch directory");
    let path = lay_out(&dir.join("program"), program);

    let output = Command::new("wasmtime")
        .arg(&path)
        .output()
        .expect("a machine to run it");
    let size = usize::try_from(fs::metadata(&path).expect("what was written").len())
        .expect("a size that fits a pointer");
    fs::remove_dir_all(&dir).expect("the scratch directory to go");

    let code = output.status.code().expect("the program was not signalled");
    (
        code,
        String::from_utf8(output.stdout).expect("what it wrote, as text"),
        size,
    )
}

fn lay_out(output: &std::path::Path, program: &Program) -> PathBuf {
    let artifacts = Wasm32Wasi.emit(program);
    assert_eq!(artifacts.len(), 1);

    let mut path = output.to_path_buf().into_os_string();
    path.push(artifacts[0].extension);
    let path = PathBuf::from(path);
    fs::write(&path, &artifacts[0].bytes).expect("somewhere to write it");

    #[cfg(unix)]
    if artifacts[0].executable {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("a runnable file");
    }
    path
}

fn status(program: &Program) -> i32 {
    execute(program).0
}

fn bytes(program: &Program) -> Vec<u8> {
    Wasm32Wasi.emit(program)[0].bytes.clone()
}

/// What every program answers, which is the same on every machine.
#[test]
fn it_answers_what_a_program_says() {
    for (name, program, answer) in programs::running() {
        assert_eq!(status(&program), answer, "{name}");
    }
}

/// And what every program writes.
#[test]
fn it_writes_what_a_program_writes() {
    for (name, program, held) in programs::printing() {
        assert_eq!(execute(&program).1, held, "{name}");
    }
}

/// Every example runs and answers what it says it does, so that one cannot
/// rot into a program that no longer reads.
#[test]
fn it_runs_every_example() {
    for entry in fs::read_dir(written()).expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let program = read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert_eq!(status(&program), 4, "{}", path.display());
    }
}

/// What each program costs here, against what it cost before.
#[test]
fn it_compiles_to_the_sizes_recorded() {
    let held = corpus()
        .into_iter()
        .map(|(name, program, size)| (name.to_owned(), program, size));
    for (name, program, size) in held.chain(examples()) {
        assert_eq!(bytes(&program).len(), size, "{name}");
    }
}

/// What this machine says it answers for is what something answers for it.
#[test]
fn it_provides_routines_that_exist() {
    for held in Wasm32Wasi.provides() {
        assert!(
            Wasm32Wasi.routines().get(held).is_some(),
            "it answers for `{held}`, which is not a routine"
        );
    }
}

/// A program of one constant, at the machine's own width.
fn wide(value: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let held = b.constant(Class::Word, value);
        b.ret(&[held])
    });
    program
}

/// And one at a width it was told.
fn narrow(bits: u16) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let held = b.constant(Class::Fixed { bits }, 1);
        b.ret(&[held])
    });
    program
}

/// What a program works out before it runs is not something this sees. A
/// program of constants is the constant it answers.
#[test]
fn it_sees_nothing_of_what_was_worked_out() {
    let arithmetic = "type Nat Zero Succ(Nat)

                      add(a Zero) -> a
                      add(a Succ(k)) -> Succ(add(a k))

                      mul(Zero b) -> Zero
                      mul(Succ(k) b) -> add(b mul(k b))

                      main!(h) ->
                        two = Succ(Succ(Zero))
                        exit!(h mul(two two))";
    let known = read(arithmetic).expect("a program");
    let four = read(
        "type Nat Zero Succ(Nat)

         main!(h) -> exit!(h Succ(Succ(Succ(Succ(Zero)))))",
    )
    .expect("a program");

    assert_eq!(status(&known), 4);
    // Nothing is left of the multiplication, nor of anything it called.
    assert_eq!(bytes(&known), bytes(&four));
}

/// A definition nothing reaches is not laid out, so a program carrying one
/// is the program without it.
#[test]
fn it_lays_out_nothing_that_is_not_reached() {
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
    let machine = read(reached).expect("a program");
    let spare = read(&spare).expect("a program");

    assert_eq!(status(&machine), 4);
    assert_eq!(bytes(&spare), bytes(&machine));
}

/// A chain of constructors is the number it builds, so a long one costs no
/// more to lay out than a short one.
#[test]
fn it_lays_out_a_chain_as_the_number_it_builds() {
    let chain = |held: usize| {
        let text = format!(
            "type Nat Zero Succ(Nat)\n\nmain!(h) -> exit!(h {}Zero{})",
            "Succ(".repeat(held),
            ")".repeat(held)
        );
        read(&text).expect("a program")
    };

    assert_eq!(status(&chain(4)), 4);
    assert_eq!(status(&chain(40)), 40);
    assert_eq!(bytes(&chain(40)).len(), bytes(&chain(4)).len());
}

/// A program built rather than written, lowered here and run. `Nat` is
/// inductive all the way to the lowering, which is where it becomes a word.
#[test]
fn it_runs_a_program_built_rather_than_written() {
    let barb = programs::two_and_two_in_barb();
    let facts = faun::barb::recognise(&barb);
    let machine =
        faun::ir::lower(&barb, &facts, &Wasm32Wasi.routines()).expect("a representable program");

    // `add` was recognised, so it is an instruction rather than a function:
    // what is left is the entry alone.
    assert_eq!(machine.functions().len(), 1, "only the entry survives");
    assert_eq!(status(&machine), 4);
}

/// A value wider than this machine's word is one it cannot hold, and a
/// narrower one is not: what a value holds above the bits it needs is
/// nought, so it goes in whatever this has.
#[test]
fn it_holds_what_a_program_holds() {
    assert!(Wasm32Wasi.accepts(&wide(70_000)).is_ok());
    assert!(Wasm32Wasi.accepts(&wide(4)).is_ok());
    assert!(Wasm32Wasi.accepts(&narrow(32)).is_ok());

    let refused = Wasm32Wasi.accepts(&narrow(33)).unwrap_err();
    assert!(
        refused.contains("holds 32 bits, and a value here needs 33"),
        "{refused}"
    );
}

/// The smallest module there is: type, function, export, code. No import
/// section at all, no memory, no data.
///
/// A program that leaves with nought compiles to the same module, since
/// `proc_exit(0)` is what running off the end of `_start` does anyway.
#[test]
fn the_smallest_module_imports_nothing() {
    assert_eq!(execute(&programs::empty()).1, "");
    let written = read(EXIT_ZERO).expect("a program");
    assert_eq!(bytes(&written), bytes(&programs::empty()));
}
