//! Shared backend conformance tests. Each target supplies its runner and size
//! baselines; every test here still runs independently against every emitter.

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::{Mutex, PoisonError};

use faun_core::ir::{Binary, Class, Op, Program, ValueId};
use faun_core::programs;
use faun_core::targets::Target;

use super::{ARITHMETIC_SIZES, CORPUS_SIZES, EXAMPLE_SIZES, LADDER_SIZES, RUNNER, TARGET};

#[path = "expressions.rs"]
mod expressions;

pub(super) const EXIT_ZERO: &str = "type Nat Zero Succ(Nat)

                                   main!(h) -> exit!(h Zero)";

fn corpus() -> [(&'static str, Program); 19] {
    [
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
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../simple/examples")
}

pub(super) fn read(text: &str) -> Result<Program, String> {
    faun_simple::read(text, &TARGET.routines())
}

pub(super) fn execute(program: &Program) -> (i32, String) {
    execute_counts(program, &[1]).remove(0)
}

fn execute_counts(program: &Program, counts: &[u16]) -> Vec<(i32, String)> {
    let cases: Vec<_> = counts.iter().map(|&count| (count, &[][..])).collect();
    execute_cases(program, &cases)
}

fn execute_with_input(program: &Program, input: &[u8]) -> (i32, String) {
    execute_cases(program, &[(1, input)]).remove(0)
}

/// Emit once, then run that artifact for each argument/input case. Exercise
/// raw emission after explicitly establishing its preconditions; integration
/// tests separately cover the checked compilation wrappers.
#[expect(
    clippy::too_many_lines,
    reason = "one test artifact's write/run/cleanup lifecycle"
)]
fn execute_cases(program: &Program, cases: &[(u16, &[u8])]) -> Vec<(i32, String)> {
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    faun_core::ir::validate(program).expect("a well-formed program");
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
    let answers = cases
        .iter()
        .map(|&(argc, input)| {
            assert!(argc >= 1, "the program name is an argument");
            let mut command = RUNNER.map_or_else(
                || Command::new(&path),
                |runner| {
                    let mut command = Command::new(runner);
                    command.arg(&path);
                    command
                },
            );
            command
                .args((1..argc).map(|_| "dummy"))
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());
            let mut child = command.spawn().expect("a machine to run it");
            child
                .stdin
                .take()
                .expect("piped stdin")
                .write_all(input)
                .expect("input for the program");
            let output = child.wait_with_output().expect("a machine to finish");
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

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one cross-target fixture covers allocation, tags, fields, calls, release, and execution"
)]
fn target_runs_managed_products_across_calls_and_matches() {
    let (mut machine, main) = Program::new("main");
    let value = machine.declare("value", &[Class::Cell], &[Class::Word]);
    machine.define(value, |b, params| {
        let tag = b.cell_tag(params[0]);
        let wanted = b.constant(Class::Word, 1);
        let matches = b.compare(faun_core::ir::Relation::Equal, tag, wanted);
        let result = b.if_(
            matches,
            &[Class::Word],
            |b| {
                let field = b.cell_field(Class::Word, params[0], 0);
                b.yield_(&[field]);
            },
            |b| {
                let zero = b.constant(Class::Word, 0);
                b.yield_(&[zero]);
            },
        )[0];
        b.ret(&[result]);
    });
    let exit = TARGET.routines().declare(&mut machine, "exit!");
    machine.define(main, |b, _| {
        let field = b.constant(Class::Word, 42);
        let cell = b.cell(1, &[field]);
        let result = b.call_one(value, &[cell]);
        b.call(exit, &[result]);
    });

    let has_cells = |program: &Program| {
        program
            .functions()
            .iter()
            .filter_map(faun_core::ir::Function::body)
            .flat_map(|body| program.every(body))
            .any(|op| {
                matches!(
                    op,
                    Op::Cell { .. } | Op::CellTag { .. } | Op::CellField { .. }
                )
            })
    };
    assert!(has_cells(&machine));
    assert!(
        (0..machine.values_count()).all(|at| machine.class(ValueId::at(at)) != Class::Natural),
        "{}",
        machine.render()
    );
    let prepared = TARGET.prepare(&machine).unwrap();
    assert!(!has_cells(&prepared));
    assert_eq!(status(&prepared), 42);
}

/// Products held flat cross calls as arguments and results, meet at a join,
/// and ride inside a sum's cell as their fields. The 6502 answers one value
/// and joins two, so there the same program also runs packed.
const PRODUCTS: &str = "type Nat Zero Succ(Nat)
                        type Bool False True
                        type Pair P(Bool Bool)
                        type Triple T(Pair Bool)
                        type Maybe Nothing Just(Triple)

                        is_zero(Zero) -> True
                        is_zero(Succ(k)) -> False
                        is_one(Zero) -> False
                        is_one(Succ(k)) -> is_zero(k)
                        and(True b) -> b
                        and(False b) -> False

                        swap(P(a b)) -> P(b a)
                        second(P(a b)) -> b
                        spin(P(a b) c) -> T(P(b c) a)
                        rotate(T(p c)) -> spin(p c)
                        choose(True t) -> rotate(t)
                        choose(False t) -> t
                        unwrap(Nothing) -> T(P(True True) True)
                        unwrap(Just(t)) -> t
                        four(True) -> Succ(Succ(Succ(Succ(Zero))))
                        four(False) -> Zero
                        status(T(p c)) -> four(and(c second(p)))

                        main!(h) ->
                          n = argc!(h)
                          flag = is_one(n)
                          start = T(swap(P(False flag)) True)
                          kept = unwrap(Just(start))
                          exit!(h status(choose(flag kept)))";

#[test]
fn products_cross_calls_joins_and_cells_as_their_fields() {
    let program = read(PRODUCTS).expect("a program holding products");
    let prepared = TARGET
        .prepare(&program)
        .expect("a program any target holds");
    // One argument: the flag is set, so the triple is rotated to
    // T(P(False True) True). Two: it is kept as T(P(True False) True).
    assert_eq!(
        execute_counts(&prepared, &[1, 2]),
        [(4, String::new()), (0, String::new())]
    );
}

/// Numbers inside a product are as wide as what is built into them, so a
/// pair of small counts is two small words: nothing allocated, and an exit
/// status proven to fit.
const NUMBER_PAIR: &str = "type Nat Zero Succ(Nat)
                           type Pair P(Nat Nat)

                           swap(P(a b)) -> P(b a)
                           sum(Zero b) -> b
                           sum(Succ(a) b) -> Succ(sum(a b))
                           both(P(a b)) -> sum(a b)
                           small(Zero) -> Zero
                           small(Succ(k)) -> Succ(Zero)

                           main!(h) ->
                             n = argc!(h)
                             p = swap(P(small(n) Succ(Succ(Zero))))
                             exit!(h both(p))";

#[test]
fn a_pair_of_small_numbers_is_two_small_words() {
    let program = read(NUMBER_PAIR).expect("a program holding a pair of numbers");
    let prepared = TARGET
        .prepare(&program)
        .expect("a program any target holds");
    assert!(
        !prepared.render().contains("allocate"),
        "{}",
        prepared.render()
    );
    assert_eq!(status(&prepared), 3);
}

/// A list built while the program runs is a buffer: counting builds one by
/// pushing in place, reversing builds another, and the first element is
/// read back from where the buffer holds it.
const LIST: &str = "type Nat Zero Succ(Nat)
                    type List Nil Cons(Nat List)

                    small(Zero) -> Zero
                    small(Succ(k)) -> Succ(Zero)
                    count(Zero acc) -> acc
                    count(Succ(k) acc) -> count(k Cons(k acc))
                    reverse(Nil acc) -> acc
                    reverse(Cons(h t) acc) -> reverse(t Cons(h acc))
                    head(Nil) -> Zero
                    head(Cons(h t)) -> h

                    main!(h) ->
                      c = argc!(h)
                      n = small(c)
                      counted = count(Succ(Succ(Succ(Succ(n)))) Nil)
                      exit!(h head(reverse(counted Nil)))";

#[test]
fn a_list_built_at_run_time_is_a_buffer() {
    let program = read(LIST).expect("a program building a list");
    let prepared = TARGET
        .prepare(&program)
        .expect("a program any target holds");
    assert!(
        prepared.render().contains("seq.reserve"),
        "{}",
        prepared.render()
    );
    assert_eq!(status(&prepared), 4);
}

/// A target's calling convention is not a language limit: preparation packs
/// what a boundary cannot carry into a cell, so these run everywhere.
#[test]
fn prepared_programs_carry_more_across_a_boundary_than_a_target_passes() {
    use programs::abi::{self, Transfer};
    let mut held = vec![abi::function(7, 3), abi::function(5, 2)];
    for kind in [Transfer::If, Transfer::LoopState, Transfer::LoopResults] {
        held.push(abi::region(kind, 3));
    }
    for program in held {
        let prepared = TARGET
            .prepare(&program)
            .expect("a program any target holds");
        assert_eq!(status(&prepared), 0);
    }
}

#[test]
fn target_supplies_named_entry_parameters() {
    let (mut program, main) = Program::new_with_params("main", &[("host", Class::Word)]);
    let exit = TARGET.routines().declare(&mut program, "exit!");
    program.define(main, |b, params| {
        b.call(exit, &[params[0]]);
    });
    faun_core::ir::validate(&program).unwrap();
    let answers = execute_counts(&program, &[1, 4, 9]);
    assert_eq!(
        answers
            .iter()
            .map(|(status, _)| *status)
            .collect::<Vec<_>>(),
        [1, 4, 9]
    );
}

/// The program a target is handed once the machine passes have read it.
///
/// Most of the corpus is measured and run as written, which is the question
/// "what does a backend do with this"; a shape only the passes produce has
/// to be asked for separately.
fn optimized(program: &Program) -> Program {
    faun_core::ir::optimize(program)
}

pub(super) fn bytes(program: &Program) -> Vec<u8> {
    TARGET.emit(program).remove(0).bytes
}

#[test]
fn it_answers_what_a_program_says() {
    for (name, program, answer) in faun_simple::programs::running() {
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
fn it_reads_standard_input_one_byte_at_a_time() {
    let program = programs::external::reads_bytes();
    assert_eq!(
        execute_with_input(&program, &[0, 127, 255]),
        (0, String::new())
    );

    let text = fs::read_to_string(written().join("stdin.fn")).expect("the stdin example");
    let source = read(&text).expect("a source program that reads a byte");
    assert_eq!(execute_with_input(&source, b"A"), (70, String::new()));
    assert_eq!(execute_with_input(&source, b""), (4, String::new()));
}

#[test]
fn it_runs_every_example() {
    for entry in fs::read_dir(written()).expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let program = read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        if path.file_stem().and_then(|name| name.to_str()) == Some("hello") {
            assert_eq!(execute(&program), (0, "Hello, world!\n".to_owned()));
        } else {
            assert_eq!(status(&program), 4, "{}", path.display());
        }
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
        let held = b.constant(Class::fixed(bits), 1);
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
    let mut barb = programs::two_and_two_in_barb();
    let machine =
        faun_core::ir::lower(barb.analyze(), &TARGET.routines()).expect("a representable program");
    // Recognized addition becomes an instruction; only the entry survives.
    assert_eq!(
        machine
            .functions()
            .iter()
            .filter_map(faun_core::ir::Function::body)
            .count(),
        1
    );
    assert_eq!(status(&machine), 4);
}

#[test]
fn guarded_argc_expressions_fold_constants_but_compute_runtime_inputs() {
    for case in expressions::CASES {
        // Normal reading keeps every optimization enabled. The guard must
        // prove scalar bounds even on targets with runtime Natural support.
        let program = read(&case.source()).expect("a guarded source expression");
        assert!(
            (0..program.values_count()).all(|at| program.class(ValueId::at(at)) != Class::Natural),
            "{case:?}: guarded arithmetic should not need runtime naturals"
        );
        let instructions: Vec<_> = program
            .functions()
            .iter()
            .filter_map(faun_core::ir::Function::body)
            .flat_map(|body| program.walk_within(body))
            .collect();
        assert!(
            instructions
                .iter()
                .any(|(op, _)| matches!(op, Op::Binary { .. })),
            "{case:?}: runtime arithmetic must survive folding"
        );
        assert!(
            !has_constant_only_multiply(&program, &instructions),
            "{case:?}: constant-only multiplication must fold"
        );
        let answers = execute_counts(&program, expressions::COUNTS);
        for (&argc, (status, stdout)) in expressions::COUNTS.iter().zip(answers) {
            assert_eq!(status, case.expected(argc), "{case:?}, argc={argc}");
            assert!(stdout.is_empty(), "{case:?}, argc={argc}: {stdout:?}");
        }
    }
}

fn has_constant_only_multiply(program: &Program, instructions: &[(&Op, &[ValueId])]) -> bool {
    let mut constants = vec![false; program.values_count()];
    for (op, results) in instructions {
        if matches!(op, Op::Constant { .. } | Op::NaturalConstant(_)) {
            constants[results[0].index()] = true;
        }
    }
    instructions.iter().any(|(op, _)| {
        matches!(
            op,
            Op::Binary {
                op: Binary::Mul,
                left,
                right,
            } if constants[left.index()] && constants[right.index()]
        )
    })
}

#[test]
fn runnable_expression_example_uses_runtime_arguments() {
    let program = read(include_str!("../../../simple/examples/expressions.fn")).unwrap();
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
    for optimized in [true, false] {
        let routines = TARGET.routines();
        let program = if optimized {
            faun_simple::read(source, &routines).unwrap()
        } else {
            // Inlining would remove the calls and joins this is about.
            let mut barb = faun_simple::parse(source, &routines).unwrap();
            faun_core::barb::validate(&barb).unwrap();
            faun_core::machine(&mut barb, &routines).unwrap()
        };
        assert!(
            (0..program.values_count())
                .any(|at| { program.class(ValueId::at(at)) == Class::fixed(0) })
        );
        let counts = [1, 2, 3, 33];
        for (argc, (status, stdout)) in counts.into_iter().zip(execute_counts(&program, &counts)) {
            assert_eq!(
                status,
                i32::from(argc == 1),
                "argc={argc}, optimized={optimized}"
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
    // Through the machine passes, because a shift is what they make of a
    // product by a power of two and nothing writes one directly.
    assert_eq!(
        status(&optimized(&programs::arithmetic::shifts_by_powers_of_two())),
        0
    );
    assert_eq!(status(&programs::arithmetic::doubles_across_bytes()), 0);
    assert_eq!(
        status(&programs::arithmetic::doubles_then_reads_the_same_number()),
        0
    );
    assert_eq!(status(&programs::arithmetic::byte_products()), 0);
    assert_eq!(status(&programs::arithmetic::widened_byte_average()), 0);
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

/// The simplest programs there are, from the tier a program arrives at.
///
/// Everything else measured here is written at the tier a target reads, so
/// it says what a backend does with IR it was handed. These say what the
/// compiler does, which is the question worth asking of a program small
/// enough that the answer can be read off the disassembly.
#[test]
fn it_compiles_the_ladder_to_the_sizes_recorded() {
    let routines = TARGET.routines();
    let ladder = programs::ladder::every(&routines);
    assert_eq!(ladder.len(), LADDER_SIZES.len());
    let changed: Vec<_> = ladder
        .into_iter()
        .zip(LADDER_SIZES)
        .filter_map(|((name, barb), &(expected, size))| {
            assert_eq!(name, expected, "size baselines must match the ladder");
            let program = lowered(barb, &routines);
            let actual = TARGET.compile(&program).expect("compilation")[0]
                .bytes
                .len();
            (actual != size).then_some((name, actual, size))
        })
        .collect();
    assert!(
        changed.is_empty(),
        "(program, actual, expected): {changed:?}"
    );
}

/// And what each of them answers, since a size nothing checks the meaning of
/// is a size anybody can reach by writing the wrong program.
#[test]
fn the_ladder_answers_what_its_programs_say() {
    // The last is far past the guard, and makes a host that lays the
    // arguments out itself write a couple of hundred bytes below wherever it
    // was told the stack is, rather than a handful. A stack pointing at the
    // wrong place shows up there and not at three arguments.
    //
    // It is 62 because every answer has to come back as an exit status:
    // twice the count is the largest of them, and wasmtime refuses to report
    // a status of 126 or above.
    const COUNTS: &[u16] = &[1, 3, 4, 5, 62];
    let routines = TARGET.routines();
    for (name, barb) in programs::ladder::every(&routines) {
        let program = lowered(barb, &routines);
        for (&argc, (status, _)) in COUNTS.iter().zip(execute_counts(&program, COUNTS)) {
            let answer = match name {
                "the count" => i32::from(argc),
                // Four past the count, and twice it, each keeping every bit
                // below the eighth and throwing the rest away.
                "the count and a constant" => i32::from(argc.wrapping_add(4) % 256),
                "the low bits of a sum" => i32::from(argc.wrapping_mul(2) % 256),
                // `a = n + 3`, `b = a + n`, then `a + b`.
                "a shared intermediate" if argc < 32 => 3 * i32::from(argc) + 6,
                "a constant" | "a shared intermediate" => 0,
                // Under the ceiling, the count, and four past it where the
                // rung asks for that. At or above it neither guarded rung
                // has the bits to say anything, so both leave with nought.
                "the count under a guard" if argc < 4 => i32::from(argc),
                _ if argc < 4 => i32::from(argc) + 4,
                _ => 0,
            };
            assert_eq!(status, answer, "{name}, argc={argc}");
        }
    }
}

/// A program as the machine tier is handed one: validated, optimized where
/// it was written, and then lowered and optimized again below.
///
/// Both halves, because a program arriving at Barb has not been through
/// Barb's own schedule yet, and lowering one that has not is lowering a
/// program nothing writes.
fn lowered(
    mut barb: faun_core::barb::Program,
    routines: &faun_core::platform::Routines,
) -> Program {
    faun_core::barb::validate(&barb).expect("a sound program");
    faun_core::barb::optimize(&mut barb);
    faun_core::machine(&mut barb, routines).expect("a representable program")
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
