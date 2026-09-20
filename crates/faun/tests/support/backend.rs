//! Shared backend conformance tests. Each target supplies its runner and size
//! baselines; every test here still runs independently against every emitter.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, PoisonError};

use faun::ir::{Binary, Class, Program};
use faun::programs;
use faun::targets::Target;

use super::{ARITHMETIC_SIZES, CORPUS_SIZES, EXAMPLE_SIZES, RUNNER, TARGET};

#[path = "expressions.rs"]
mod expressions;

pub(super) const EXIT_ZERO: &str = "type Nat Zero Succ(Nat)

                                   main!(h) -> exit!(h Zero)";

fn corpus() -> [(&'static str, Program); 20] {
    [
        ("empty", programs::empty()),
        ("exit zero", read(EXIT_ZERO).expect("a program")),
        ("two and two", programs::two_and_two()),
        ("hello world", programs::hello_world()),
        ("a call", programs::calls_a_function()),
        ("recursion", programs::recurses()),
        ("values across a call", programs::values_survive_a_call()),
        ("the heap", programs::uses_the_heap()),
        ("a byte", programs::stores_a_byte()),
        ("a global", programs::counts_in_a_global()),
        ("writing the heap", programs::writes_from_the_heap()),
        (
            "a computed length",
            programs::writes_a_length_it_worked_out(),
        ),
        ("eight bits", programs::wraps_at_eight_bits()),
        ("less", programs::less(7, 9)),
        ("two worked out", programs::compares_two_worked_out_values()),
        ("a flag", programs::branches_on_a_flag_it_read()),
        ("a countdown", programs::countdown(3)),
        ("a carried total", programs::carries_a_total_into_an_arm(3)),
        ("a step first", programs::counts_down_before_it_branches(3)),
        ("a long arm", programs::a_branch_over_a_long_arm(40, true)),
    ]
}

fn written() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

pub(super) fn read(text: &str) -> Result<Program, String> {
    faun::read(text, &TARGET.routines())
}

pub(super) fn execute(program: &Program) -> (i32, String) {
    execute_counts(program, &[1]).remove(0)
}

/// Emit once, then run that same artifact with each argument count. Exercise
/// raw emission after explicitly establishing its preconditions; integration
/// tests separately cover the checked compilation wrappers.
#[expect(
    clippy::too_many_lines,
    reason = "one test artifact's write/run/cleanup lifecycle"
)]
fn execute_counts(program: &Program, counts: &[u16]) -> Vec<(i32, String)> {
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    faun::ir::validate(program).expect("a well-formed program");
    TARGET
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
    let artifacts = TARGET.emit(program);
    assert_eq!(artifacts.len(), 1);
    let artifact = &artifacts[0];
    let path = dir.join(format!("program{}", artifact.extension));
    fs::write(&path, &artifact.bytes).expect("somewhere to write it");
    #[cfg(unix)]
    if artifact.executable {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("a runnable file");
    }
    let answers = counts
        .iter()
        .map(|&argc| {
            assert!(argc >= 1, "the program name is an argument");
            let mut command = RUNNER.map_or_else(
                || Command::new(&path),
                |runner| {
                    let mut command = Command::new(runner);
                    command.arg(&path);
                    command
                },
            );
            command.args((1..argc).map(|_| "dummy"));
            let output = command.output().expect("a machine to run it");
            let code = output.status.code().unwrap_or_else(|| {
                panic!(
                    "the program was signalled: {}",
                    String::from_utf8_lossy(&output.stderr)
                )
            });
            (
                code,
                String::from_utf8(output.stdout).expect("what it wrote, as text"),
            )
        })
        .collect();
    fs::remove_dir_all(&dir).expect("the scratch directory to go");
    answers
}

pub(super) fn status(program: &Program) -> i32 {
    execute(program).0
}

pub(super) fn bytes(program: &Program) -> Vec<u8> {
    TARGET.emit(program).remove(0).bytes
}

#[test]
fn it_answers_what_a_program_says() {
    for (name, program, answer) in programs::running() {
        assert_eq!(status(&program), answer, "{name}");
    }
}

#[test]
fn it_writes_what_a_program_writes() {
    for (name, program, held) in programs::printing() {
        assert_eq!(execute(&program).1, held, "{name}");
    }
}

#[test]
fn it_runs_every_example() {
    for entry in fs::read_dir(written()).expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let program = read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert_eq!(status(&program), 4, "{}", path.display());
    }
}

#[test]
fn it_compiles_to_the_sizes_recorded() {
    let corpus = corpus();
    assert_eq!(corpus.len(), CORPUS_SIZES.len());
    let held =
        corpus
            .into_iter()
            .zip(CORPUS_SIZES)
            .map(|((name, program), &(expected_name, size))| {
                assert_eq!(name, expected_name, "size baselines must match the corpus");
                (name, program, size)
            });
    let examples = EXAMPLE_SIZES.iter().map(|&(name, size)| {
        let text = fs::read_to_string(written().join(format!("{name}.fn"))).expect("an example");
        let program = read(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
        (name, program, size)
    });
    let changed: Vec<_> = held
        .chain(examples)
        .filter_map(|(name, program, size)| {
            let actual = bytes(&program).len();
            (actual != size).then_some((name, actual, size))
        })
        .collect();
    assert!(
        changed.is_empty(),
        "(program, actual, expected): {changed:?}"
    );
}

#[test]
fn it_provides_routines_that_exist() {
    for held in TARGET.provides() {
        assert!(
            TARGET.routines().get(held).is_some(),
            "it answers for `{held}`, which is not a routine"
        );
    }
}

pub(super) fn wide(value: u64) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let held = b.constant(Class::Word, value);
        b.ret(&[held]);
    });
    program
}

pub(super) fn narrow(bits: u16) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let held = b.constant(Class::Fixed { bits }, 1);
        b.ret(&[held]);
    });
    program
}

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
    assert_eq!(bytes(&known), bytes(&four));
}

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

#[test]
fn it_runs_a_program_built_rather_than_written() {
    let barb = programs::two_and_two_in_barb();
    let facts = faun::barb::analyze(&barb);
    let machine =
        faun::ir::lower(&barb, &facts, &TARGET.routines()).expect("a representable program");
    // Recognized addition becomes an instruction; only the entry survives.
    assert_eq!(
        machine
            .functions()
            .iter()
            .filter_map(faun::ir::Function::body)
            .count(),
        1
    );
    assert_eq!(status(&machine), 4);
}

#[test]
fn guarded_argc_expressions_fold_constants_but_compute_runtime_inputs() {
    use faun::ir::{Op, ValueId};

    for case in expressions::CASES {
        // Normal reading keeps every optimization enabled. The guard must
        // prove scalar bounds even on targets with runtime Natural support.
        let program = read(&case.source()).expect("a guarded source expression");
        assert!(
            (0..program.values_count()).all(|at| program.class(ValueId::at(at)) != Class::Natural),
            "{case:?}: guarded arithmetic should not need runtime naturals"
        );
        let ops: Vec<_> = program
            .functions()
            .iter()
            .filter_map(faun::ir::Function::body)
            .flat_map(|body| program.every(body))
            .collect();
        assert!(
            ops.iter().any(|op| matches!(op, Op::Binary { .. })),
            "{case:?}: runtime arithmetic must survive folding"
        );
        assert!(
            !ops.iter().any(|op| matches!(
                op,
                Op::Binary {
                    op: Binary::Mul,
                    ..
                }
            )),
            "{case:?}: constant-only multiplication must fold"
        );
        let answers = execute_counts(&program, expressions::COUNTS);
        for (&argc, (status, stdout)) in expressions::COUNTS.iter().zip(answers) {
            assert_eq!(status, case.expected(argc), "{case:?}, argc={argc}");
            assert!(stdout.is_empty(), "{case:?}, argc={argc}: {stdout:?}");
        }
    }
}

#[test]
fn runnable_expression_example_uses_runtime_arguments() {
    let program = read(include_str!("../../../../examples/expressions.fn")).unwrap();
    let counts = [1, 2, 3, 31, 32, 33];
    for (argc, (status, stdout)) in counts.into_iter().zip(execute_counts(&program, &counts)) {
        let expected = if argc < 32 {
            2 * i32::from(argc) + 2
        } else {
            0
        };
        assert_eq!(status, expected, "argc={argc}");
        assert!(stdout.is_empty());
    }
}

#[test]
fn source_zero_width_scalars_cross_calls_and_joins() {
    let source = include_str!("zero_width.fn");
    for inline_helpers in [true, false] {
        let program = faun::read_with_options(
            source,
            &TARGET.routines(),
            &faun::barb::OptimizeOptions {
                inline_helpers,
                ..faun::barb::OptimizeOptions::default()
            },
        )
        .unwrap();
        assert!(
            (0..program.values_count())
                .any(|at| { program.class(faun::ir::ValueId::at(at)) == Class::Fixed { bits: 0 } })
        );
        let counts = [1, 2, 3, 33];
        for (argc, (status, stdout)) in counts.into_iter().zip(execute_counts(&program, &counts)) {
            assert_eq!(
                status,
                i32::from(argc == 1),
                "argc={argc}, inline={inline_helpers}"
            );
            assert!(stdout.is_empty());
        }
    }
}

#[test]
fn runtime_arithmetic_boundaries_and_odd_widths() {
    // Parameters force runtime selection; callees compare the full result.
    for bits in [0, 1, 2, 3, 7, 8, 9, 15, 16, 31, 32, 33, 63, 64] {
        if bits > TARGET.word() {
            continue;
        }
        for op in [Binary::Mul, Binary::Div, Binary::Mod] {
            assert_eq!(
                status(&programs::arithmetic::boundaries(bits, op)),
                0,
                "{bits} {op:?}"
            );
        }
    }
    assert_eq!(status(&programs::arithmetic::odd_conversion()), 0);
    assert_eq!(status(&programs::arithmetic::zero_conversion()), 0);
    assert_eq!(status(&programs::arithmetic::preserves_host_count()), 0);
}

#[test]
fn runtime_arithmetic_varied_inputs() {
    // Deterministic 16-bit inputs, checked by the host's unsigned model.
    let mut seed = 0xD371u16;
    let pairs: Vec<_> = (0..64)
        .map(|_| {
            seed = seed.wrapping_mul(25173).wrapping_add(13849);
            let left = u64::from(seed);
            seed = seed.wrapping_mul(25173).wrapping_add(13849);
            (left, u64::from(seed))
        })
        .collect();
    for op in [Binary::Mul, Binary::Div, Binary::Mod] {
        let inputs: Vec<_> = pairs
            .iter()
            .map(|&(a, b)| {
                if op == Binary::Mul {
                    (a & 255, b & 255)
                } else {
                    (a, b)
                }
            })
            .collect();
        for chunk in inputs.chunks(8) {
            assert_eq!(
                status(&programs::arithmetic::cases(16, op, chunk)),
                0,
                "{op:?} {chunk:?}"
            );
        }
    }
}

#[test]
fn structured_completion_preserves_returns_and_skipped_effects() {
    for condition in [0, 1] {
        for p in [
            programs::control::entry_returns(condition),
            programs::control::function_returns(condition),
        ] {
            assert_eq!(status(&p), if condition == 0 { 17 } else { 42 });
        }
        let (status, output) = execute(&programs::control::early_success(condition));
        assert_eq!(status, 0);
        assert_eq!(output, if condition == 0 { "continued\n" } else { "" });
    }
}

#[test]
fn external_declarations_interleave_with_internal_function_ids() {
    let (status, stdout) = execute(&programs::external::interleaved());
    assert_eq!(status, 42);
    assert_eq!(stdout, "externals\n");
}

#[test]
fn runtime_arithmetic_size_ratchets() {
    // One runtime call, full-result comparison, startup and image headers.
    // Detect reintroduced value-counting regions above the targets.
    for (op, expected) in [Binary::Mul, Binary::Div, Binary::Mod]
        .into_iter()
        .zip(ARITHMETIC_SIZES)
    {
        let program = programs::arithmetic::cases(16, op, &[(65535, 1)]);
        assert_eq!(bytes(&program).len(), expected, "{op:?}");
    }
}
