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
#[path = "faun.rs"]
mod faun;

pub(super) const EXIT_ZERO: &str = "import std.host {Host}

                                   main! : Host -> []
                                   main!(host) -> host.exit!(0)";

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
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../core/tests/support/examples")
}

/// Compile a Faun program for this target through the primary frontend.
pub(super) fn read(text: &str) -> Result<Program, String> {
    faun::lower(text, &TARGET)
}

/// The same, lowered without optimizing.
pub(super) fn read_unoptimized(text: &str) -> Result<Program, String> {
    faun::unoptimized(text, &TARGET)
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
    let dir = scratch("faun");
    let path = TARGET
        .write(&TARGET.emit(program), &dir.join("program"))
        .expect("somewhere to write it");
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

/// Files by name, as a program finds or leaves them where it runs.
type Directory = std::collections::BTreeMap<String, Vec<u8>>;

/// Emit `program` and run it where `files` lie, in a directory of their
/// own: the status it exits with, and the files as it left them. A WASI
/// runner is handed that directory as the one the program runs in.
fn execute_among(program: &Program, files: &Directory) -> (i32, Directory) {
    let dir = scratch("faun-files");
    let work = dir.join("work");
    fs::create_dir_all(&work).expect("a directory to run in");
    for (name, bytes) in files {
        fs::write(work.join(name), bytes).expect("a file to start with");
    }
    let path = TARGET
        .write(&TARGET.emit(program), &dir.join("program"))
        .expect("somewhere to write it");
    let mut command = RUNNER.map_or_else(
        || Command::new(&path),
        |runner| {
            let mut command = Command::new(runner);
            if runner == "wasmtime" {
                command.args(["run", "--dir", "."]);
            }
            command.arg(&path);
            command
        },
    );
    let output = command
        .current_dir(&work)
        .stdin(Stdio::null())
        .output()
        .expect("a machine to run it");
    let code = output.status.code().expect("a program that exits");
    let left = fs::read_dir(&work)
        .expect("the files it left")
        .map(|entry| {
            let entry = entry.expect("a file it left");
            (
                entry.file_name().into_string().expect("a name"),
                fs::read(entry.path()).expect("what it holds"),
            )
        })
        .collect();
    fs::remove_dir_all(&dir).expect("the scratch directory to go");
    (code, left)
}

/// A directory of its own, made, named for this process and the moment.
fn scratch(prefix: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "{prefix}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("a clock after the epoch")
            .as_nanos()
    ));
    fs::create_dir_all(&dir).expect("a scratch directory");
    dir
}

/// Every way a file is opened, beneath where the program runs, as
/// `files.fn` says, and nothing made where there is nothing to read.
#[test]
fn it_opens_files_beneath_where_it_runs() {
    let program = read(include_str!("files.fn")).expect("a program that opens files");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let input: Directory = [("input.txt".to_owned(), b"from the file\n".to_vec())].into();
    let (code, left) = execute_among(&program, &input);
    assert_eq!(code, 0);
    let expected: Directory = [
        ("created.txt".to_owned(), Vec::new()),
        ("input.txt".to_owned(), b"from the file\n".to_vec()),
        ("output.txt".to_owned(), b"from the file\n+tail".to_vec()),
    ]
    .into();
    assert_eq!(left, expected);
    // Nothing to read: the first open fails, and nothing is made.
    assert_eq!(
        execute_among(&program, &Directory::new()),
        (2, Directory::new())
    );
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
                let word = b.shape(&[Class::Word]);
                let field = b.cell_field((Class::Word, word), params[0], 0);
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
        let word = b.shape(&[Class::Word]);
        let cell = b.cell(1, word, &[field]);
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

/// Removing a temporary product must leave both uses of its managed field
/// alive. The two calls still share one inner cell after forwarding.
#[test]
fn forwarded_managed_fields_survive_both_calls() {
    let (mut machine, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
    let read = machine.declare("read", &[Class::Cell], &[Class::Word]);
    machine.define(read, |b, args| {
        let shape = b.shape(&[Class::Word]);
        let value = b.cell_field((Class::Word, shape), args[0], 0);
        b.ret(&[value]);
    });
    machine.define(main, |b, args| {
        let word = b.shape(&[Class::Word]);
        let cells = b.shape(&[Class::Cell; 2]);
        let inner = b.cell(7, word, &[args[0]]);
        let outer = b.cell(0, cells, &[inner, inner]);
        let left = b.cell_field((Class::Cell, cells), outer, 0);
        let right = b.cell_field((Class::Cell, cells), outer, 1);
        let first = b.call_one(read, &[left]);
        let second = b.call_one(read, &[right]);
        let answer = b.binary(Binary::Add, first, second);
        b.ret(&[answer]);
    });
    faun_core::ir::validate(&machine).unwrap();
    let optimized = faun_core::ir::optimize(&machine);
    let body = optimized.function(main).body().unwrap();
    assert_eq!(
        optimized
            .every(body)
            .filter(|op| matches!(op, Op::Cell { .. }))
            .count(),
        1
    );
    assert!(
        !optimized
            .every(body)
            .any(|op| matches!(op, Op::CellField { .. }))
    );
    let prepared = TARGET.prepare(&optimized).unwrap();
    assert_eq!(
        execute_counts(&prepared, &[1, 2]),
        [(2, String::new()), (4, String::new())]
    );
}

/// Products held flat cross calls as arguments and results, meet at a join,
/// and ride inside a sum's cell as their fields. The 6502 answers one value
/// and joins two, so there the same program also runs packed.
const PRODUCTS: &str = "import std.host {Host}

                        Pair : [P(Bool, Bool)]
                        Triple : [T(Pair, Bool)]
                        Maybe : [Nothing, Just(Triple)]

                        is_one : Nat -> Bool
                        is_one(1) -> True
                        is_one(_) -> False

                        swap : Pair -> Pair
                        swap(P(a, b)) -> P(b, a)

                        second : Pair -> Bool
                        second(P(_, b)) -> b

                        spin : (Pair, Bool) -> Triple
                        spin(P(a, b), c) -> T(P(b, c), a)

                        rotate : Triple -> Triple
                        rotate(T(p, c)) -> spin(p, c)

                        choose : (Bool, Triple) -> Triple
                        choose(True, t) -> rotate(t)
                        choose(False, t) -> t

                        unwrap : Maybe -> Triple
                        unwrap(Nothing) -> T(P(True, True), True)
                        unwrap(Just(t)) -> t

                        status : Triple -> Nat
                        status(T(p, c)) -> c.and(second(p)).select(4, 0)

                        main! : Host -> []
                        main!(host) -> (
                          count = host.args.len()
                          flag = is_one(count)
                          start = T(swap(P(False, flag)), True)
                          kept = unwrap(Just(start))
                          host.exit!(U8.of_nat(status(choose(flag, kept))))
                        )";

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
const NUMBER_PAIR: &str = "import std.host {Host}

                           Pair : [P(Nat, Nat)]

                           swap : Pair -> Pair
                           swap(P(a, b)) -> P(b, a)

                           both : Pair -> Nat
                           both(P(a, b)) -> a + b

                           small : Nat -> Nat
                           small(0) -> 0
                           small(Succ(_)) -> 1

                           main! : Host -> []
                           main!(host) -> (
                             count = host.args.len()
                             p = swap(P(small(count), 2))
                             host.exit!(U8.of_nat(both(p)))
                           )";

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
const LIST: &str = "import std.host {Host}

                    small : Nat -> Nat
                    small(0) -> 0
                    small(Succ(_)) -> 1

                    count : (Nat, List(Nat)) -> List(Nat)
                    count(0, acc) -> acc
                    count(Succ(k), acc) -> count(k, [k, *acc])

                    turn : (List(Nat), List(Nat)) -> List(Nat)
                    turn([], acc) -> acc
                    turn([h, *t], acc) -> turn(t, [h, *acc])

                    head : List(Nat) -> Nat
                    head([]) -> 0
                    head([h, *_]) -> h

                    main! : Host -> []
                    main!(host) -> (
                      c = host.args.len()
                      n = small(c)
                      counted = count(4 + n, [])
                      host.exit!(U8.of_nat(head(turn(counted, []))))
                    )";

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

/// A list's length is what its buffer says it holds: counting one reads
/// that, and walks nothing.
const LENGTH: &str = "import std.host {Host}

                      small : Nat -> Nat
                      small(0) -> 0
                      small(Succ(_)) -> 1

                      count : (Nat, List(Nat)) -> List(Nat)
                      count(0, acc) -> acc
                      count(Succ(k), acc) -> count(k, [k, *acc])

                      main! : Host -> []
                      main!(host) -> host.exit!(U8.of_nat(count(4 + small(host.args.len()), []).len()))";

#[test]
fn a_list_is_counted_by_the_length_it_holds() {
    let program = read(LENGTH).expect("a program counting a list");
    let prepared = TARGET
        .prepare(&program)
        .expect("a program any target holds");
    assert!(
        !prepared.render().contains("List.len"),
        "{}",
        prepared.render()
    );
    assert_eq!(status(&prepared), 5);
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

/// Excess arguments and multiple results may be packed or stack-passed,
/// but every occurrence of the same managed value still owns its claim.
#[test]
fn managed_aliases_survive_wide_calls_and_multiple_results() {
    let (mut program, main) = Program::new("main");
    let wide = program.declare("wide", &[Class::Cell; 8], &[Class::Cell; 4]);
    program.define(wide, |b, args| b.ret(&[args[7], args[0], args[6], args[1]]));
    program.define(main, |b, _| {
        let word = b.shape(&[Class::Word]);
        let value = b.constant(Class::Word, 21);
        let cell = b.cell(0, word, &[value]);
        let first = b.call(wide, &[cell; 8]);
        let second = b.call(wide, &[first[3]; 8]);
        let left = b.cell_field((Class::Word, word), first[0], 0);
        let right = b.cell_field((Class::Word, word), second[3], 0);
        let sum = b.binary(Binary::Add, left, right);
        b.ret(&[sum]);
    });
    let prepared = TARGET.prepare(&program).unwrap();
    assert_eq!(status(&prepared), 42);
}

#[test]
fn target_supplies_named_entry_parameters() {
    let (mut program, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
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

/// A startup value nothing reads is not an entry parameter, so the target
/// never produces it.
#[test]
fn an_unread_startup_value_is_never_produced() {
    let reads = read(
        "import std.host {Host}
         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(host.args.len()))",
    )
    .expect("a program reading argc");
    assert_eq!(
        reads.parameter_names(reads.entry()).collect::<Vec<_>>(),
        ["argc"]
    );
    let ignores = read(EXIT_ZERO).expect("a program ignoring argc");
    assert_eq!(ignores.parameter_names(ignores.entry()).count(), 0);
}

/// The program a target is handed once the machine passes have read it.
///
/// Most of the corpus is measured and run as written, which is the question
/// "what does a backend do with this"; a shape only the passes produce has
/// to be asked for separately.
fn optimized(program: &Program) -> Program {
    faun_core::ir::optimize(program)
}

/// The image `program` makes favouring size, which the sizes recorded
/// here hold to: a build favouring speed may spend bytes on it.
pub(super) fn bytes(program: &Program) -> Vec<u8> {
    TARGET.emit_with(
        program,
        faun_core::targets::Favour::Size,
        faun_core::targets::SymbolTable::Omitted,
    )
}

/// Every program here and what it leaves with. What a program answers is a
/// fact about the program, so it is said once rather than once per
/// machine, and every target has to answer the same.
fn running() -> Vec<(&'static str, Program, i32)> {
    let mut held = built();
    for (name, leave, answer) in [
        ("an arm that comes back", false, 2),
        ("an arm that leaves", true, 1),
    ] {
        let mut barb = programs::an_arm_that_leaves(leave);
        faun_core::barb::optimize(&mut barb);
        let machine = faun_core::lower_to_machine_ir(&barb, &TARGET.routines()).expect("a program");
        held.push((name, machine, answer));
    }
    for (name, text, answer) in WRITTEN {
        let program = read(text).unwrap_or_else(|error| panic!("{name}: {error}\n{text}"));
        held.push((name, program, *answer));
    }
    held
}

/// The programs built in machine IR, and what each leaves with.
fn built() -> Vec<(&'static str, Program, i32)> {
    vec![
        ("two and two", programs::two_and_two(), 4),
        (
            "a long arm first",
            programs::a_branch_over_a_long_arm(40, true),
            40,
        ),
        (
            "a long arm last",
            programs::a_branch_over_a_long_arm(40, false),
            40,
        ),
        ("a global", programs::counts_in_a_global(), 3),
        ("eight bits", programs::wraps_at_eight_bits(), 4),
        (
            "values across a call",
            programs::values_survive_a_call(),
            45,
        ),
        (
            "a comparison",
            programs::compares_two_worked_out_values(),
            1,
        ),
        ("a flag it read", programs::branches_on_a_flag_it_read(), 7),
        (
            "a total into an arm",
            programs::carries_a_total_into_an_arm(3),
            3,
        ),
    ]
}

/// Programs written in Faun and what each leaves with.
const WRITTEN: &[(&str, &str, i32)] = &[
    ("exit zero", EXIT_ZERO, 0),
    (
        "a status it was told",
        "import std.host {Host}
         main! : Host -> []
         main!(host) -> host.exit!(3)",
        3,
    ),
    (
        "a name that leaves",
        "import std.host {Host}
         die! : (Host, Nat) -> []
         die!(host, n) -> host.exit!(U8.of_nat(n))
         main! : Host -> []
         main!(host) -> die!(host, 2)",
        2,
    ),
    (
        "a tag from a count",
        "import std.host {Host}
         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(True.to_nat()))",
        1,
    ),
    (
        "how many arguments",
        "import std.host {Host}
         below : (Nat, Nat) -> Bool
         below(_, 0) -> False
         below(0, Succ(_)) -> True
         below(Succ(a), Succ(b)) -> below(a, b)
         finish! : (Host, Bool, Nat) -> []
         finish!(host, True, n) -> host.exit!(U8.of_nat(n + n))
         finish!(host, False, _) -> host.exit!(0)
         main! : Host -> []
         main!(host) -> (
           count = host.args.len()
           finish!(host, below(count, 2), count)
         )",
        2,
    ),
    (
        "a runtime guard exits early",
        "import std.host {Host}
         below : (Nat, Nat) -> Bool
         below(_, 0) -> False
         below(0, Succ(_)) -> True
         below(Succ(a), Succ(b)) -> below(a, b)
         finish! : (Host, Bool, Nat) -> []
         finish!(host, True, n) -> host.exit!(U8.of_nat(n))
         finish!(host, False, _) -> host.exit!(7)
         main! : Host -> []
         main!(host) -> (
           count = host.args.len()
           finish!(host, below(count, 1), count)
         )",
        7,
    ),
    ("a tag", ORDER_LT, 0),
    ("a tag", ORDER_GT, 2),
    ("two columns", COLUMNS_MONUS, 2),
    ("two columns", COLUMNS_UNDERFLOW, 0),
    ("two columns", COLUMNS_LESS, 0),
    ("two columns", COLUMNS_SAME, 1),
    ("two columns", COLUMNS_MORE, 2),
    ("runtime addition", ARITHMETIC_ADD, 11),
    ("runtime monus", ARITHMETIC_MONUS, 7),
    ("runtime underflow", ARITHMETIC_UNDERFLOW, 0),
    ("runtime multiplication", ARITHMETIC_MUL, 18),
    ("runtime division", ARITHMETIC_DIV, 4),
    ("runtime remainder", ARITHMETIC_MOD, 1),
    ("runtime division by zero", ARITHMETIC_DIV_ZERO, 0),
    ("runtime remainder by zero", ARITHMETIC_MOD_ZERO, 9),
    ("runtime less than", ARITHMETIC_LESS, 1),
    ("runtime equality", ARITHMETIC_EQUAL, 1),
    ("runtime inequality", ARITHMETIC_UNEQUAL, 0),
];

/// A tag read back as the constructor it is.
macro_rules! ordering {
    ($which:literal) => {
        concat!(
            "import std.host {Host}
             Place : [First, Second, Third]
             rank : Place -> Nat
             rank(First) -> 0
             rank(Second) -> 1
             rank(Third) -> 2
             pick : Nat -> Place
             pick(0) -> First
             pick(Succ(_)) -> Third
             main! : Host -> []
             main!(host) -> host.exit!(U8.of_nat(rank(pick(",
            $which,
            "))))"
        )
    };
}
const ORDER_LT: &str = ordering!("0");
const ORDER_GT: &str = ordering!("1");

/// Two columns matched at once. Subtraction stops at nought rather than
/// wrapping, which is what the second column buys.
macro_rules! columns {
    ($answer:literal) => {
        concat!(
            "import std.host {Host}
             sub : (Nat, Nat) -> Nat
             sub(0, _) -> 0
             sub(Succ(m), 0) -> Succ(m)
             sub(Succ(m), Succ(n)) -> sub(m, n)
             cmp : (Nat, Nat) -> Order
             cmp(0, 0) -> Eq
             cmp(0, Succ(_)) -> Lt
             cmp(Succ(_), 0) -> Gt
             cmp(Succ(m), Succ(n)) -> cmp(m, n)
             rank : Order -> Nat
             rank(Lt) -> 0
             rank(Eq) -> 1
             rank(Gt) -> 2
             main! : Host -> []
             main!(host) -> host.exit!(U8.of_nat(",
            $answer,
            "))"
        )
    };
}
const COLUMNS_MONUS: &str = columns!("sub(3, 1)");
const COLUMNS_UNDERFLOW: &str = columns!("sub(1, 3)");
const COLUMNS_LESS: &str = columns!("rank(cmp(1, 3))");
const COLUMNS_SAME: &str = columns!("rank(cmp(3, 3))");
const COLUMNS_MORE: &str = columns!("rank(cmp(3, 1))");

/// Runtime arithmetic: the count cannot fold, and the guard is what makes
/// what follows fit even on the smallest target.
macro_rules! arithmetic {
    ($answer:literal) => {
        concat!(
            "import std.host {Host}
             below : (Nat, Nat) -> Bool
             below(_, 0) -> False
             below(0, Succ(_)) -> True
             below(Succ(a), Succ(b)) -> below(a, b)
             finish! : (Host, Bool, Nat) -> []
             finish!(host, False, _) -> host.exit!(0)
             finish!(host, True, n) -> (
               a = n + 8
               b = n + 1
               z = n - n
               host.exit!(U8.of_nat(",
            $answer,
            "))
             )
             main! : Host -> []
             main!(host) -> (
               count = host.args.len()
               finish!(host, below(count, 2), count)
             )"
        )
    };
}
const ARITHMETIC_ADD: &str = arithmetic!("a + b");
const ARITHMETIC_MONUS: &str = arithmetic!("a - b");
const ARITHMETIC_UNDERFLOW: &str = arithmetic!("b - a");
const ARITHMETIC_MUL: &str = arithmetic!("a * b");
const ARITHMETIC_DIV: &str = arithmetic!("a / b");
const ARITHMETIC_MOD: &str = arithmetic!("a % b");
const ARITHMETIC_DIV_ZERO: &str = arithmetic!("a / z");
const ARITHMETIC_MOD_ZERO: &str = arithmetic!("a % z");
const ARITHMETIC_LESS: &str = arithmetic!("below(b, a).to_nat()");
const ARITHMETIC_EQUAL: &str = arithmetic!("a.equals(a).to_nat()");
const ARITHMETIC_UNEQUAL: &str = arithmetic!("a.equals(b).to_nat()");

/// The standard list's functions over `[0, 1, 2, 3, 4]`, whose last element
/// is worked out while the program runs so that nothing here is folded
/// before a target sees it.
macro_rules! listed {
    ($answer:literal) => {
        concat!(
            "import std.host {Host}
             small : Nat -> Nat
             small(0) -> 0
             small(Succ(_)) -> 1
             main! : Host -> []
             main!(host) -> (
               n = 4 + small(host.args.len())
               xs = [0, 1, 2, 3, n - 1]
               host.exit!(U8.of_nat(",
            $answer,
            "))
             )"
        )
    };
}
const LIST_GET: &str = listed!("xs.get(3).ok_or(9) + xs.get(n).ok_or(9) * 10");
const LIST_SET: &str = listed!("xs.set(1, 7).ok_or([]).get_or(1, 0)");
const LIST_FIND: &str =
    listed!("xs.find(|x| x % 2 == 1).ok_or(9) + xs.find(|x| x == 7).ok_or(9) * 10");
const LIST_FILTER: &str = listed!("xs.filter(|x| x % 2 == 1).len()");
const LIST_DROP_TAKE: &str = listed!("xs.drop(1).take(2).get_or(1, 9)");
const LIST_TAKE_PAST: &str = listed!("xs.take(9).len()");
const LIST_LAST: &str = listed!("xs.last().ok_or(9)");
// A list put before itself, which its buffer is shared with.
const LIST_CONCAT: &str = listed!("xs.concat(xs).get_or(6, 9) * 10 + xs.concat(xs).get_or(9, 9)");
const LIST_REVERSE: &str = listed!("xs.reverse().get_or(0, 9) * 10 + xs.reverse().get_or(4, 9)");
// Elements that are lists themselves, each holding a claim to its buffer.
// What a list of lists holds is not bounded, so the answer is made to fit.
const LIST_OF_LISTS: &str = listed!(
    "([xs, xs.drop(3)].reverse().get_or(0, []).get_or(0, 9) % 10) + ([[xs], [xs.drop(4)]].flatten().get_or(1, []).get_or(0, 9) % 10) * 10"
);

/// Programs using the standard list, and what each leaves with. A lookup
/// that can miss answers a `Result`, which a target holds as a cell, so
/// each is prepared before it runs.
const LISTED: &[(&str, &str, i32)] = &[
    ("a list read at an index", LIST_GET, 93),
    ("a list with an element replaced", LIST_SET, 7),
    ("a list searched", LIST_FIND, 91),
    ("a list filtered and counted", LIST_FILTER, 2),
    ("a list dropped from and taken from", LIST_DROP_TAKE, 2),
    ("a list taken past its end", LIST_TAKE_PAST, 5),
    ("the last of a list", LIST_LAST, 4),
    ("a list put before itself", LIST_CONCAT, 14),
    ("a list reversed", LIST_REVERSE, 40),
];

/// Lists of lists reversed and flattened: elements holding a claim to a
/// buffer of their own, and a count of them no bound is known for.
#[test]
fn lists_of_lists_are_put_before_one_another() {
    let program = read(LIST_OF_LISTS).expect("a program");
    let prepared = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(status(&prepared), 43);
}

#[test]
fn the_standard_list_answers_what_a_program_says() {
    for (name, text, answer) in LISTED {
        let program = read(text).unwrap_or_else(|error| panic!("{name}: {error}\n{text}"));
        let prepared = TARGET
            .prepare(&program)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(status(&prepared), *answer, "{name}");
    }
}

#[test]
fn it_answers_what_a_program_says() {
    for (name, program, answer) in running() {
        assert_eq!(status(&program), answer, "{name}");
    }
}

#[test]
fn it_writes_what_a_program_writes() {
    for (name, program, held) in programs::printing() {
        assert_eq!(execute(&program).1, held, "{name}");
    }
}

/// Lists of every kind of element, built from a number the program is
/// handed so nothing is worked out before it runs, then joined, reversed,
/// mapped and compared: bools, bytes, pairs of a small number and a wider
/// one, strings, lists of lists, and records holding strings. Each element
/// is laid out as it is, so each kind is its own layout. Two at a time, so
/// each program is small enough for every machine.
#[test]
fn lists_of_every_element_hold_what_they_were_given() {
    const KINDS: &str = "held : Bool -> Nat
         held(True) -> 1
         held(False) -> 0

         bools : Nat -> Bool
         bools(n) -> [n == 1, n == 2, True].reverse() == [True, False, True]

         bytes : Nat -> Bool
         bytes(n) -> \"xy${n}\".to_utf8().reverse() == \"1yx\".to_utf8()

         pairs : Nat -> Bool
         pairs(n) -> [(n, 300 + n), (2, 5)].map(|(small, wide)| small + wide) == [302, 7]

         strings : Nat -> Bool
         strings(n) -> [\"a${n}\", \"bb\", \"c\"].concat([\"d\"]).reverse() == [\"d\", \"c\", \"bb\", \"a1\"]

         nested : Nat -> Bool
         nested(n) -> [[n, 2], [3]].concat([[4, 5, 6]]).map(|xs| xs.len()) == [2, 1, 3]

         records : Nat -> Bool
         records(n) -> named([{name: \"a${n}\", size: n}, {name: \"b\", size: 2}])

         named : List({name: Str, size: Nat}) -> Bool
         named(held) -> held.map(|r| r.name) == [\"a1\", \"b\"] & held.map(|r| r.size) == [1, 2]";
    for (first, second) in [
        ("bools", "bytes"),
        ("pairs", "nested"),
        ("strings", "records"),
    ] {
        let text = format!(
            "import std.host {{Host}}

             main! : Host -> []
             main!(host) -> (
               n = host.args.len() % 4
               host.exit!(U8.of_nat(held({first}(n)) + held({second}(n)) * 2))
             )

             {KINDS}"
        );
        let program = read(&text).unwrap_or_else(|e| panic!("{first}: {e}"));
        let program = TARGET
            .prepare(&program)
            .unwrap_or_else(|e| panic!("{first}: {e}"));
        assert_eq!(status(&program), 3, "{first} and {second}");
    }
}

/// A list is written where it lies where nothing else holds it, and copied
/// first where something does, which then reads what it held: numbers and
/// strings, each replaced in a list threaded through a fold and in one held
/// twice, and a position past the end refused.
#[test]
fn a_list_set_where_nothing_else_holds_it_is_written_in_place() {
    let text = "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           n = host.args.len() % 4
           host.exit!(U8.of_nat(held(threaded(n)) + held(shared(n)) * 2 + held(strings(n)) * 4 + held(past(n)) * 8))
         )

         held : Bool -> Nat
         held(True) -> 1
         held(False) -> 0

         threaded : Nat -> Bool
         threaded(n) -> List.range(n + 5).fold(List.repeat(0, n + 5), |xs, i| xs.set(i, i * i).ok_or([])) == [0, 1, 4, 9, 16, 25]

         shared : Nat -> Bool
         shared(n) -> (
           xs = [n, 2, 3]
           ys = xs.set(0, 7).ok_or([])
           xs == [1, 2, 3] & ys == [7, 2, 3]
         )

         strings : Nat -> Bool
         strings(n) -> (
           names = [\"a${n}\", \"b\", \"c\"]
           renamed = names.set(1, \"d${n}\").ok_or([])
           again = renamed.set(2, \"e\").ok_or([])
           names == [\"a1\", \"b\", \"c\"] & again == [\"a1\", \"d1\", \"e\"]
         )

         past : Nat -> Bool
         past(n) -> [n].set(n, 5).is_err()";
    let program = read(text).expect("a program");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(status(&program), 15);
}

/// Memory two and four bytes wide, as well as a byte and a word.
#[test]
fn it_stores_narrower_than_a_word() {
    let program = programs::stores_narrower_than_a_word(TARGET.word());
    assert_eq!(status(&program), 6);
}

#[test]
fn it_reads_standard_input() {
    // The primitive a program's reading is built on, one byte at a time.
    let program = programs::external::reads_bytes();
    assert_eq!(
        execute_with_input(&program, &[0, 127, 255]),
        (0, String::new())
    );

    // All of it, as a program asks: what goes to standard error is not
    // what goes to standard output.
    let text = fs::read_to_string(written().join("stdin.fn")).expect("the stdin example");
    let source = read(&text).expect("a source program that reads its input");
    let source = TARGET
        .prepare(&source)
        .expect("a program this machine holds");
    assert_eq!(execute_with_input(&source, b"AB"), (6, "AB".to_owned()));
    assert_eq!(execute_with_input(&source, b""), (4, String::new()));

    // Far more than the heap a program starts with holds: where a target
    // has more to give, the heap grows into it.
    if TARGET.word() > 16 {
        // A status a WASI runner passes on, which is below 126.
        let long = vec![b'x'; 100_100];
        let (status, echoed) = execute_with_input(&source, &long);
        assert_eq!(status, (100_100 + 4) % 256);
        assert_eq!(echoed.len(), long.len());
    }
}

/// An `if` works out only the branch it chooses, so the recursion its
/// other branch would start never begins, and a branch may be a block of
/// its own; the count of arguments says which branch runs.
#[test]
fn an_if_works_out_only_the_branch_it_chooses() {
    let program = read(
        "import std.host {Host}

         count : Nat -> Nat
         count(n) -> if n == 0 then 0 else 1 + count(n - 1)

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           answer = if n > 1 then 99 else (
             more = n + 4
             count(more)
           )
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program choosing a branch");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [5, 99]);
}

/// A test binds where it holds: along its `&` chain and into `then`, a
/// tuple tested whole, and a list by its end; the count of arguments picks
/// the way it goes.
#[test]
fn a_test_binds_where_it_holds() {
    let program = read(
        "import std.host {Host}

         parsed : Nat -> Result(Nat, [Few])
         parsed(n) -> if n > 1 then Ok(n * 10) else Err(Few)

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           r = parsed(n)
           a = if r is Ok(v) & v < 25 then v else 1
           b = if (r, n) is (Ok(_), 2) then 2 else 3
           c = if [n, n + 1] is [*_, last] then last else 0
           host.exit!(U8.of_nat(a + b + c))
         )",
    )
    .expect("a program testing what it has");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2, 3])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [1 + 3 + 2, 20 + 2 + 3, 1 + 3 + 4]);
}

/// An `expect` line goes on where its condition holds, with what it bound,
/// and leaves where it fails, from a clause and from a branch answering it.
#[test]
fn an_expect_goes_on_or_leaves() {
    let program = read(
        "import std.host {Host}

         first_or : (List(Nat), Nat) -> Nat
         first_or(xs, fallback) -> (
           xs is [x, *_] else return fallback
           x * 10
         )

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           listed = if n > 1 then [n] else []
           answer = first_or(listed, 7)
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program leaving early");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [7, 20]);
}

/// A pattern names a whole value and takes it apart, compares with a name
/// by `==name`, and a guard's test, and names both sides of an `|` bind,
/// are seen by what follows.
#[test]
fn patterns_name_wholes_compare_and_bind_from_guards() {
    let program = read(
        "import std.host {Host}

         merge : (List(Nat), List(Nat)) -> List(Nat)
         merge([], right) -> right
         merge(left, []) -> left
         merge([x, *xs], right is [y, *_]) if x <= y -> [x, *merge(xs, right)]
         merge(left is [_, *_], [y, *ys]) -> [y, *merge(left, ys)]

         lookup : (List(Nat), Nat) -> Nat
         lookup(xs, i) if xs.get(i) is Ok(found) -> found
         lookup(_, _) -> 0

         either : (Result(Nat, [Gone]), Result(Nat, [Gone])) -> Nat
         either(a, b) -> if a is Ok(v) | b is Ok(v) then v else 1

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           merged = merge([n, 5], [2, 4])
           second = lookup(merged, 1)
           found = if merged is [_, ==n, *_] then 100 else 0
           tried = if n > 1 then Ok(n) else Err(Gone)
           answer = second + found + either(Err(Gone), tried) * 10
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program naming wholes, comparing and binding from guards");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [12, 122]);
}

/// An arm leaves where `then` would stand: `return` answers the clause,
/// `continue` and `break` the loop, from arms that are a binding's value
/// and from arms on a line of their own, which go on with `{}`.
#[test]
fn an_arm_may_leave() {
    let program = read(
        "import std.host {Host}

         picked : List(Nat) -> Nat
         picked(xs) -> (
           for x in xs do (
             step = x is (
               0 break
               1 continue
               n if n > 2 return n
               n then n
             )
             x is (
               2 return step * 10
               _ then {}
             )
           )
           9
         )

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           answer = picked([1, n + 1, 0, 7]) + picked([0, 5])
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program whose arms leave");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [29, 12]);
}

/// An `is` with arms answers by the first arm whose pattern matches and
/// whose guard holds, as a value the body goes on from and as a clause's
/// answer.
#[test]
fn arms_answer_by_the_first_that_matches() {
    let program = read(
        "import std.host {Host}

         Shape : [Circle(Nat), Square(Nat), Dot]

         area : Shape -> Nat
         area(shape) -> shape is (
           Circle(r) then 3 * r * r
           Square(s) then s * s
           Dot then 0
         )

         sized : List(Nat) -> Nat
         sized(xs) -> xs.first() is (
           Ok(n) if n > 1 then 100
           Ok(1 | 0) then 10
           Ok(_) then 5
           Err(_) then 1
         )

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           shape = if n > 1 then Square(n) else Dot
           counted = sized([n]) + sized([])
           answer = area(shape) + counted
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program choosing by arms");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [11, 105]);
}

/// A branch whose value goes on into more of the body may leave by `?`
/// or a line's `else`, the rest of the body going on from each branch that
/// does not.
#[test]
fn a_branch_whose_value_goes_on_may_leave() {
    let program = read(
        "import std.host {Host}

         parsed : (Bool, Str) -> Result(Nat, [Malformed])
         parsed(strict, text) -> (
           n = if strict then Nat.from_str(text)? else 3
           Ok(n + 1)
         )

         scaled : (Nat, Nat) -> Nat
         scaled(n, k) -> (
           step = (
             k > 0 else return 7
             n / k
           )
           step * 10
         )

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           text = if n > 1 then \"x\" else \"5\"
           tried = parsed(True, text).ok_or(9) + parsed(False, text).ok_or(9)
           answer = tried + scaled(4, n - 1)
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program leaving from branches");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [17, 53]);
}

/// A branch, an arm or a `return` that never answers takes the type the
/// others answer: where it is taken the program ends with its status, and
/// where it is not the program goes on with the other's value.
#[test]
fn a_way_that_never_answers_meets_one_that_does() {
    let program = read(
        "import std.host {Host}

         fail! : (Host, Nat) -> []
         fail!(host, status) -> host.exit!(U8.of_nat(status))

         port! : (Host, Str) -> Nat
         port!(host, text) -> (
           Nat.from_str(text) is Ok(n) else return host.exit!(6)
           n
         )

         main! : Host -> []
         main!(host) -> (
           count = host.args.len()
           n = if count > 1 then 3 else host.exit!(2)
           p = port!(host, if count == 3 then \"x\" else \"1\")
           m = count is (
             2 | 3 then 4
             _ then fail!(host, 5)
           )
           host.exit!(U8.of_nat(n + p + m))
         )",
    )
    .expect("a program whose ways never answer");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2, 3, 4])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [2, 8, 6, 5]);
}

/// A name assigned again holds its new value from there on, past the
/// branch or arm it was assigned in.
#[test]
fn an_assigned_name_holds_its_new_value_past_its_branch() {
    let program = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           count = n
           count = count * 10
           label = if n > 1 then (
             count = count + 5
             1
           ) else 2
           seen = host.args is (
             [_, *_] then (
               count = count + label
               True
             )
             [] then False
           )
           host.exit!(U8.of_nat(count))
         )",
    )
    .expect("a program assigning names");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers: Vec<_> = execute_counts(&program, &[1, 2])
        .into_iter()
        .map(|(status, _)| status)
        .collect();
    assert_eq!(answers, [12, 26]);
}

/// A loop runs its round once for each element, or while its condition
/// holds, carrying what it binds again from round to round; an effect in
/// a round happens each round, in order; and `continue`, `break` and
/// `return` leave the round, the loop and the clause.
#[test]
fn loops_carry_names_and_keep_their_effects_in_order() {
    let program = read(
        "import std.host {Host, Stdout, IoError}

         counted! : (Stdout, Nat) -> Result(Nat, IoError)
         counted!(out, n) -> (
           total = 0
           for x in List.range(n + 3) do (
             if x == 4 break
             x % 2 == 1 else continue
             written = out.write_all!(\"${x};\".to_utf8())?
             total = total + x
           )
           ready = [5, 6]
           while ready is [head, *rest] do (
             ready = rest
             if head > 5 return Ok(total * 10 + head)
           )
           Ok(total)
         )

         main! : Host -> []
         main!(host) -> (
           tried = counted!(host.stdout, host.args.len())
           answer = tried.ok_or(99)
           host.exit!(U8.of_nat(answer))
         )",
    )
    .expect("a program with loops");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers = execute_counts(&program, &[1, 2]);
    assert_eq!(answers, [(46, "1;3;".to_owned()), (46, "1;3;".to_owned())]);
}

/// The arguments a program is run with are a list of strings, its own name
/// first: a greeting names the first after it, or the world where there is
/// none, and the count is how many there are.
#[test]
fn it_greets_whom_it_is_handed() {
    let program = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           name = host.args.get_or(1, \"world\")
           host.println!(\"Hello, ${name}!\")
           host.exit!(U8.of_nat(host.args.len()))
         )",
    )
    .expect("a program reading its arguments");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let counts = [1, 2, 3];
    let greeted: Vec<_> = counts
        .iter()
        .map(|&count| (i32::from(count), if count == 1 { "world" } else { "dummy" }))
        .map(|(count, name)| (count, format!("Hello, {name}!\n")))
        .collect();
    assert_eq!(execute_counts(&program, &counts), greeted);
}

/// The strings a program is handed are byte strings whatever else it holds:
/// a list of numbers built beside them is not taken for their type.
#[test]
fn it_is_handed_strings_beside_a_list_of_numbers() {
    let program = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           name = host.args.get_or(1, \"world\")
           sizes = [name.len(), host.args.len()]
           host.println!(\"Hello, ${name}!\")
           host.exit!(U8.of_nat((sizes.len() + sizes.sum()) % 8))
         )",
    )
    .expect("a program reading its arguments");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(
        execute_counts(&program, &[2]),
        [((2 + 5 + 2) % 8, "Hello, dummy!\n".to_owned())]
    );
}

/// Advent of Code 2015, day one, on an input far longer than a stack of
/// frames goes: each step calls the next in tail position, which is a loop.
/// A 16-bit machine's heap holds a shorter walk, still past its frames.
#[test]
fn a_long_walk_goes_round_rather_than_down() {
    let steps = if TARGET.word() == 16 { 300 } else { 20_000 };
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../faun/examples/aoc/201501.fn");
    let text = fs::read_to_string(&path).expect("the day one example");
    let program = read(&text).expect("the day one example compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let input = "(()".repeat(steps);
    assert_eq!(
        execute_with_input(&program, input.as_bytes()),
        (0, format!("Ok({{part1: {steps}, part2: 0}})\n"))
    );
}

/// Walks building a list on the way out, `[f(x), *walk(rest)]`, on a list
/// far longer than a stack of frames goes: each is built front to back in a
/// loop, a filter skipping elements and a walk answering its list beside a
/// state as well.
#[test]
fn a_list_built_on_the_way_out_goes_round_rather_than_down() {
    let length: u64 = if TARGET.word() == 16 { 300 } else { 200_000 };
    let text = format!(
        "import std.host {{Host}}

         doubled : List(Nat) -> List(Nat)
         doubled([]) -> []
         doubled([x, *rest]) -> [x + x, *doubled(rest)]

         odd : List(Nat) -> List(Nat)
         odd([]) -> []
         odd([x, *rest]) if x % 2 == 1 -> [x, *odd(rest)]
         odd([_, *rest]) -> odd(rest)

         running : (List(Nat), Nat) -> (Nat, List(Nat))
         running([], total) -> (total, [])
         running([x, *rest], total) -> (
           (last, totals) = running(rest, total + x)
           (last, [total, *totals])
         )

         main! : Host -> []
         main!(host) -> (
           xs = List.range({length} + host.args.len() - 1)
           (last, totals) = running(odd(xs), 0)
           both = doubled(xs).len() + totals.len()
           host.exit!(U8.of_nat((both + last) % 100))
         )"
    );
    let program = read(&text).expect("the walks compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    // Every element doubled, the odd half, and the odd ones summed, kept
    // below the statuses WASI refuses.
    let half = length / 2;
    let odd_sum = half.pow(2);
    let status = (length + half + odd_sum) % 100;
    assert_eq!(
        execute(&program),
        (i32::try_from(status).expect("a byte"), String::new())
    );
}

/// A loop inside another, for more rounds of the outer than a stack of
/// frames goes: where the inner one ends, the outer goes round, and a
/// `return` inside the inner one leaves both. Each is a loop of the
/// function holding it, not a call of the outer from inside the inner;
/// three deep too, with a `continue` at every depth or at none.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one program's four nests of loops, each a shape that must go round"
)]
fn a_loop_inside_another_goes_round_rather_than_down() {
    let rounds: u64 = if TARGET.word() == 16 { 300 } else { 200_000 };
    let text = format!(
        "import std.host {{Host}}

         marked : Nat -> Nat
         marked(count) -> (
           seen = List.repeat(False, count)
           groups = []
           for start in List.range(count) do (
             if start % 2 == 1 continue
             stack = [start]
             while stack is [*stack, node] do (
               seen = seen.put(node, True)
             )
             groups = groups.append(1)
           )
           groups.len() + seen.count(|mark| mark)
         )

         first_past : (Nat, Nat) -> Nat
         first_past(count, limit) -> (
           for start in List.range(count) do (
             if start % 2 == 1 continue
             stack = [start]
             while stack is [*stack, node] do (
               if node >= limit return node
             )
           )
           0
         )

         nested : Nat -> Nat
         nested(count) -> (
           total = 0
           for a in List.range(count) do (
             for b in [a, a + 1] do (
               stack = [b]
               while stack is [*stack, node] do (
                 total = total + 1
               )
             )
           )
           total
         )

         skipping : Nat -> Nat
         skipping(count) -> (
           total = 0
           for a in List.range(count) do (
             if a % 2 == 1 continue
             for b in [a, a] do (
               if b % 4 == 2 continue
               stack = [b]
               while stack is [*stack, node] do (
                 if node % 8 == 4 continue
                 total = total + 1
               )
             )
           )
           total
         )

         main! : Host -> []
         main!(host) -> (
           count = {rounds} + host.args.len() - 1
           two = marked(count) + first_past(count, count - 2)
           three = nested(count) + skipping(count)
           host.exit!(U8.of_nat((two + three) % 100))
         )"
    );
    let program = read(&text).expect("the loops compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    // Every other start marks one node and adds a group, and the last even
    // start is the first past the limit. Three deep, every start counts
    // twice, or, skipping, only every eighth does.
    let two = rounds + rounds - 2;
    let three = 2 * rounds + 2 * ((rounds - 1) / 8 + 1);
    let status = (two + three) % 100;
    assert_eq!(
        execute(&program),
        (i32::try_from(status).expect("a byte"), String::new())
    );
}

/// Exercise day 18's row kernel with runtime cells on every target. The
/// complete application exceeds sim65's 64 KiB code space; the larger
/// targets also run its expectations and both hundred-step stdin solvers.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one example's kernel, expectations and stdin cases, with a smaller fixture for sim65"
)]
fn the_animated_lights_run_on_each_target() {
    let text = include_str!("../../../faun/examples/aoc/201518.fn");
    let kernel = text.replace(
        "main!(host) -> host.run_stdin!(app)",
        "main!(host) -> (
           cell = U8.of_nat(host.args.len() % 2)
           row = [cell, 1, cell]
           next = row.map2(row_sums(row), |current, total| next_light(current, total - current))
           ordinary = next.count(|light| light == 1)
           stuck = corner_row(next, True).count(|light| light == 1)
           host.exit!(U8.of_nat(ordinary * 10 + stuck))
    )",
    );
    let program = read(&kernel).expect("the day 18 row kernel compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(
        execute_counts(&program, &[1, 2, 3, 4]),
        [13, 2, 13, 2].map(|status| (status, String::new()))
    );
    if TARGET.word() == 16 {
        return;
    }

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../faun/examples/aoc/201518.fn");
    let program = faun::expectations_at(&path, &TARGET).expect("the day 18 expectations compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(execute(&program), (0, String::new()));

    let program = read(text).expect("the day 18 example compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    for (input, expected) in [
        ("##\n##\n", "Ok({part1: 4, part2: 4})\n"),
        ("..\n..\n", "Ok({part1: 0, part2: 4})\n"),
        ("#\n", "Ok({part1: 0, part2: 1})\n"),
        ("..\n.\n", "Err(UnequalRows)\n"),
    ] {
        assert_eq!(
            execute_with_input(&program, input.as_bytes()),
            (0, expected.to_owned()),
            "{input:?}"
        );
    }
}

/// Exercise day 19's overlapping replacement walk on every target. The
/// full parser and hash set exceed sim65's code space; the larger targets
/// also run all expectations and both parts on input read from stdin.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one example's replacement kernel, expectations and stdin cases, scaled for sim65"
)]
fn the_medicine_replacements_run_on_each_target() {
    let text = include_str!("../../../faun/examples/aoc/201519.fn");
    let kernel = text.replace(
        "main!(host) -> host.run_stdin!(app)",
        "main!(host) -> (
           count = host.args.len()
           rule = Rule(\"AA\".to_utf8(), \"B\".to_utf8())
           made = replace_each(rule, [], List.repeat('A', count), [])
           valid = made.all(|molecule| molecule.len() == count - 1 & molecule.count(|byte| byte == 'B') == 1)
           host.exit!(U8.of_nat(valid.select(made.len(), 99) % 256))
    )",
    );
    let program = read(&kernel).expect("the day 19 replacement kernel compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(
        execute_counts(&program, &[1, 2, 3, 4]),
        [0, 1, 2, 3].map(|status| (status, String::new()))
    );
    if TARGET.word() == 16 {
        return;
    }

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../faun/examples/aoc/201519.fn");
    let program = faun::expectations_at(&path, &TARGET).expect("the day 19 expectations compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(execute(&program), (0, String::new()));

    let program = read(text).expect("the day 19 example compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    for (input, expected) in [
        (
            "e => H\ne => O\nH => HO\nH => OH\nO => HH\n\nHOH\n",
            "Ok({part1: 4, part2: 3})\n",
        ),
        (
            "e => H\ne => O\nH => HO\nH => OH\nO => HH\n\nHOHOHO\n",
            "Ok({part1: 7, part2: 6})\n",
        ),
        ("e => AAA\nAA => B\n\nAAA", "Ok({part1: 2, part2: 1})\n"),
        (
            "e => H\nH => HH\nH => HH\n\nHH",
            "Ok({part1: 1, part2: 2})\n",
        ),
        ("e => AB\nAB => C\n\nC", "Ok({part1: 0, part2: 2})\n"),
        (
            "e => H\nH => AB\nX => AB\n\nAB",
            "Ok({part1: 0, part2: 2})\n",
        ),
        ("e => A\nA => B\nB => A\n\nC", "Err(Unfabricable)\n"),
        ("H -> O\n\nH", "Err(MalformedRule)\n"),
    ] {
        assert_eq!(
            execute_with_input(&program, input.as_bytes()),
            (0, expected.to_owned()),
            "{input:?}"
        );
    }
    // Every rule raises the additive weight by one, and expanding the
    // leading A forty times constructs this target: 41 is a proven minimum.
    let input = format!("e => AB\nA => ARnBYBAr\n\nA{}B", "RnBYBAr".repeat(40));
    assert_eq!(
        execute_with_input(&program, input.as_bytes()),
        (0, "Ok({part1: 41, part2: 41})\n".to_owned())
    );
}

/// The fabrication search's priority queue orders runtime costs on all
/// three targets, including sim65 where the complete search cannot fit.
#[test]
fn the_medicine_queue_orders_estimated_costs() {
    let text = include_str!("../../../faun/examples/aoc/201519.fn").replace(
        "main!(host) -> host.run_stdin!(app)",
        "ordered : (Work, Nat, Nat) -> Bool
         ordered(Empty, _, 0) -> True
         ordered(Queued(cost, _, _, left, right), expected, Succ(fuel)) if cost == expected ->
           ordered(merge_work(left, right), expected + 1, fuel)
         ordered(_, _, _) -> False

         main!(host) -> (
           queue = List.range(6).fold(Empty, |queue, at|
             merge_work(Queued((at + host.args.len()) % 6, at, [], Empty, Empty), queue))
           host.exit!(U8.of_nat(ordered(queue, 0, 6).select(0, 1)))
         )",
    );
    let program = read(&text).expect("the medicine queue compiles");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(
        execute_counts(&program, &[1, 2, 3, 4, 5, 6]),
        std::array::from_fn::<_, 6, _>(|_| (0, String::new()))
    );
}

/// A package's expectations, built as `faun test` builds them, say which
/// do not hold, whatever the target: here the third.
#[test]
fn it_runs_a_packages_expectations() {
    let text = "bucket : Nat -> Nat
                bucket(0) -> 0
                bucket(1 | 2) -> 1
                bucket(_) -> 2

                total : Str -> Nat
                total(text) -> text.split(\",\").map(|piece| Nat.from_str(piece.trim()).ok_or(0)).sum()

                expect bucket(2) == 1 & bucket(7) == 2
                expect total(\"3, 4,5\") == 12
                expect [3, 1, 2].sort() == [3, 2, 1]
                expect \"b\\na\".lines().sort() == [\"a\", \"b\"]

                main!(host) -> host.exit!(9)";
    let program = faun::expectations(text, &TARGET).expect("the expectations compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(execute(&program), (0, "3 ".to_owned()));
}

/// Generated builder lambdas share a span but keep their own identities,
/// including when their arguments contain callbacks capturing runtime data.
#[test]
fn generated_callbacks_keep_their_identities() {
    let text = r#"both : (Result(a, e), Result(b, e), (a, b) -> c) -> Result(c, e)
                  both(Ok(x), Ok(y), f) -> Ok(f(x, y))
                  both(Err(e), _, _) -> Err(e)
                  both(_, Err(e), _) -> Err(e)

                  built : Nat -> Result({a: Nat, b: Nat, c: Bool}, [Malformed])
                  built(n) -> both({a: Ok([n, 2].map(|x| x + n).sum()), b: Ok(n + 3), c: Ok(True)})

                  show(x) -> "${x}"

                  main!(host) -> (
                    n = host.args.len()
                    r = built(n).ok_or({a: 0, b: 0, c: False})
                    host.println!("${show(r.a)} ${r.b.to_str()} ${r.c}")
                    host.exit!(0)
                  )"#;
    let program = read(text).expect("generated callbacks lower to first-order IR");
    let program = TARGET
        .prepare(&program)
        .expect("the target holds the program");
    assert_eq!(
        execute_counts(&program, &[1, 3]),
        [(0, "5 4 True\n".to_owned()), (0, "11 6 True\n".to_owned())]
    );
}

/// The standard library holds every expectation it has of itself, whatever
/// the target.
#[test]
fn the_standard_library_holds_its_expectations() {
    let program = faun::expectations_at(::faun::standard_path(), &TARGET)
        .expect("the standard expectations compile");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(execute(&program), (0, String::new()));
}

#[test]
fn it_runs_every_example() {
    for entry in fs::read_dir(written()).expect("the examples") {
        let path = entry.expect("an example").path();
        let text = fs::read_to_string(&path).expect("an example to read");
        let program = read(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let program = TARGET
            .prepare(&program)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
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
    let routines = TARGET.routines();
    for held in TARGET.provides() {
        assert!(
            routines.get(held).is_some() || routines.startup(held).is_some(),
            "it answers for `{held}`, which is neither a routine nor a startup value"
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
    let known = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           two = 2
           host.exit!(U8.of_nat(two * two))
         )",
    )
    .expect("a program");
    let four = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> host.exit!(4)",
    )
    .expect("a program");
    assert_eq!(status(&known), 4);
    assert_eq!(bytes(&known), bytes(&four));
}

#[test]
fn it_lays_out_nothing_that_is_not_reached() {
    let reached = "import std.host {Host}

                   double : Nat -> Nat
                   double(n) -> n + n

                   main! : Host -> []
                   main!(host) -> host.exit!(U8.of_nat(double(2)))";
    let spare = format!(
        "{reached}

         quadruple : Nat -> Nat
         quadruple(n) -> double(double(n))

         quadruple_again : Nat -> Nat
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
            "import std.host {{Host}}\n\nmain! : Host -> []\nmain!(host) -> host.exit!(U8.of_nat({}0{}))",
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
    let machine = faun_core::ir::lower(&barb, &TARGET.routines()).expect("a representable program");
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

/// A `U64`'s sum, difference and product are taken modulo 2^64, and the
/// exact answer of each can pass sixty-four bits: they are worked out at
/// sixty-four bits all the same, wrapping, with no natural anywhere, and
/// answer what the ring does on every target. One argument and three: a
/// product past the word, and a difference below nought, each answering
/// its top six bits, which every bit below carries into.
#[test]
fn a_sixty_four_bit_words_arithmetic_wraps_in_the_machine() {
    let program = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           n = U64.of_nat(host.args.len())
           state = n * 0x5851f42d4c957f2d + 0x14057b7ef767814f
           below = n - 2
           mixed = (state ^ below) * 0x100000001b3 - state
           host.exit!(mixed.shift_right(58).to_u8())
         )",
    )
    .expect("a program of words");
    assert!(
        (0..program.values_count()).all(|at| program.class(ValueId::at(at)) != Class::Natural),
        "a word's arithmetic should not need runtime naturals"
    );
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers = execute_counts(&program, &[1, 3]);
    let statuses: Vec<_> = answers.iter().map(|(status, _)| *status).collect();
    assert_eq!(statuses, [31, 18]);
}

/// A narrower word's `of_nat` takes a natural modulo a power of two, and
/// keeping the bits below it is reading the natural's low word: no
/// remainder is left to work out, and the words answer what the ring does
/// on every target, for a natural below 2^64 and one past it. The status
/// is halved, since wasmtime refuses one past 125.
#[test]
fn a_narrower_words_of_nat_reads_the_low_bits() {
    let program = read(
        "import std.host {Host}

         main! : Host -> []
         main!(host) -> (
           n = (host.args.len() - 1) * 0x1000000000000000000 + 0xfedcba9876543210 + host.args.len()
           small = U8.of_nat(n).to_nat() + U16.of_nat(n).to_nat()
           word = U32.of_nat(n).shift_right(24).to_nat() + U64.of_nat(n).shift_right(56).to_nat()
           host.exit!(U8.of_nat(small + word).shift_right(1))
         )",
    )
    .expect("a program of words");
    let body = program.function(program.entry()).body().expect("a body");
    let remainders = program
        .every(body)
        .filter(|op| {
            matches!(
                op,
                Op::Binary {
                    op: Binary::Mod,
                    ..
                }
            )
        })
        .count();
    assert_eq!(remainders, 0, "keeping the low bits should not divide");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    let answers = execute_counts(&program, &[1, 3]);
    let statuses: Vec<_> = answers.iter().map(|(status, _)| *status).collect();
    let expected: Vec<_> = [1u128, 3]
        .iter()
        .map(|&count| {
            let n = (count - 1) * (1 << 72) + 0xfedc_ba98_7654_3210 + count;
            let small = n % (1 << 8) + n % (1 << 16);
            let word = ((n % (1 << 32)) >> 24) + ((n % (1 << 64)) >> 56);
            i32::try_from(((small + word) % 256) >> 1).expect("a byte")
        })
        .collect();
    assert_eq!(statuses, expected);
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

/// A number with no bound, worked out and written in decimal: past what any
/// word holds, so every target reaches for its natural runtime.
#[test]
fn a_number_past_every_word_is_worked_out_and_written() {
    let program = read(
        "import std.host {Host}

         fact : (Nat, Nat) -> Nat
         fact(0, acc) -> acc
         fact(Succ(n), acc) -> fact(n, acc * (n + 1))

         main! : Host -> []
         main!(host) -> (
           said = host.stdout.write_all!(\"${fact(host.args.len() + 29, 1)}\\n\".to_utf8())
           host.exit!(0)
         )",
    )
    .expect("a program with an unbounded number");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    assert_eq!(
        execute(&program),
        (0, "265252859812191058636308480000000\n".to_owned())
    );
}

/// A function holding more at once than an index register reaches in a
/// small machine's frame: two hundred values, each the count times a
/// number of its own, all wanted after a call, then added up.
#[test]
fn a_frame_holds_more_than_an_index_reaches() {
    const HELD: u64 = 200;
    let (mut program, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
    let echo = program.declare("echo", &[Class::Word], &[Class::Word]);
    program.define(echo, |b, params| b.ret(&[params[0]]));
    program.define(main, |b, params| {
        let argc = params[0];
        let held: Vec<_> = (1..=HELD)
            .map(|at| {
                let at = b.constant(Class::Word, at);
                b.binary(Binary::Mul, argc, at)
            })
            .collect();
        // A call, which each held value outlives, so none can sit anywhere
        // a callee might write.
        let echoed = b.call_one(echo, &[argc]);
        let total = held
            .iter()
            .fold(echoed, |total, &value| b.binary(Binary::Add, total, value));
        // A status wasmtime passes on is below 126.
        let modulus = b.constant(Class::Word, 97);
        let status = b.binary(Binary::Mod, total, modulus);
        b.ret(&[status]);
    });
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    // One argument: one, and one to two hundred, is 20101.
    let expected = (1 + HELD * (HELD + 1) / 2) % 97;
    assert_eq!(execute(&program).0, i32::try_from(expected).unwrap());
}

/// A number past what the word holds is held as words, and answers what it
/// would whole: a sum, a product, a difference, a quotient by a small number
/// and an order, each past sixteen bits, which the 6502's word is.
#[test]
fn a_number_wider_than_the_word_is_held_as_words() {
    let program = read(
        "import std.host {Host}

         above : (Nat, Nat) -> Nat
         above(x, limit) if x > limit -> 1
         above(_, _) -> 0

         main! : Host -> []
         main!(host) -> (
           n = host.args.len() + 70000
           m = n + n
           p = n * 3
           d = p - n
           q = p / 7
           host.exit!(U8.of_nat(above(m, 140001) + 2 * above(p, 210002) + 4 * above(d, 140001) + 8 * above(q, 30000) + 16 * above(m, 140002)))
         )",
    )
    .expect("a program with numbers wider than a small word");
    let program = TARGET
        .prepare(&program)
        .expect("a program this machine holds");
    // One argument: 70001, twice 140002, thrice 210003, less once 140002,
    // over seven 30000.
    assert_eq!(execute(&program).0, 7);
}

/// A known string is laid out once, however long: its bytes are in the
/// image as they are, so a longer one costs its bytes and nothing more, and
/// a walk over it reads them there.
#[test]
fn a_long_known_string_is_laid_out_once() {
    let program = |length: usize| {
        let source = format!(
            "import std.host {{Host}}

             found : Bool -> Nat
             found(True) -> 1
             found(False) -> 0

             main! : Host -> []
             main!(host) -> (
               bytes = \"{}b\".to_utf8()
               host.exit!(U8.of_nat(found(bytes.contains(98)) * 100 + bytes.len() % 100))
             )",
            "a".repeat(length)
        );
        let program = read(&source).expect("a program holding a long string");
        TARGET
            .prepare(&program)
            .expect("a program this machine holds")
    };
    let (short, long) = (program(1000), program(4000));
    let grown = bytes(&long).len() - bytes(&short).len();
    assert!(grown < 2 * 3000, "3000 more bytes of text took {grown}");
    assert_eq!(execute(&long).0, 101);
}

#[test]
fn runnable_expression_example_uses_runtime_arguments() {
    let program = read(include_str!("examples/expressions.fn")).unwrap();
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

/// A known-zero scalar is still an argument, a result and a branch result.
/// Computing it calls argc again: knowing the result must not erase that
/// call.
const ZERO_WIDTH: &str = "import std.host {Host}

                          keep_zero! : (Host, Nat) -> Nat
                          keep_zero!(host, n) -> (
                            observed = host.args.len()
                            n
                          )

                          select_zero! : (Host, Bool) -> Nat
                          select_zero!(host, False) -> keep_zero!(host, 0)
                          select_zero!(host, True) -> keep_zero!(host, 0)

                          zero_or_one : (Bool, Nat) -> Nat
                          zero_or_one(False, n) -> n
                          zero_or_one(True, n) -> Succ(n)

                          main! : Host -> []
                          main!(host) -> (
                            count = host.args.len()
                            first = count.equals(1)
                            z = select_zero!(host, first)
                            host.exit!(U8.of_nat(zero_or_one(first, z)))
                          )";

#[test]
fn source_zero_width_scalars_cross_calls_and_joins() {
    let source = ZERO_WIDTH;
    for optimized in [true, false] {
        let program = if optimized {
            read(source).unwrap()
        } else {
            // Inlining would remove the calls and joins this is about.
            read_unoptimized(source).unwrap()
        };
        assert!(
            (0..program.values_count())
                .any(|at| { program.class(ValueId::at(at)) == Class::fixed(0) })
        );
        // Unoptimized, the host is handed on whole, arguments and all.
        let program = TARGET
            .prepare(&program)
            .expect("a program this machine holds");
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
        for op in [
            Binary::Monus,
            Binary::Mul,
            Binary::Div,
            Binary::Mod,
            Binary::And,
            Binary::Or,
            Binary::Xor,
        ] {
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

/// Shifts by a distance the program is handed: one instruction where a
/// target has one and the distance is known to be below its word, and a
/// loop of one-place shifts otherwise, wider than a word among them.
#[test]
fn runtime_shifts_by_a_distance() {
    for bits in [1, 2, 7, 8, 9, 15, 16, 31, 32, 33, 63, 64] {
        if bits > TARGET.word() {
            continue;
        }
        let max = u64::MAX >> (64 - bits);
        let top = u64::from(bits - 1);
        for op in [Binary::ShiftUp, Binary::ShiftDown] {
            let mut pairs = vec![(0, 0), (max, 0), (1, top), (0, top), (max, top)];
            if op == Binary::ShiftUp {
                pairs.retain(|&(value, by)| {
                    value
                        .checked_shl(u32::try_from(by).unwrap())
                        .is_some_and(|moved| moved <= max && moved >> by == value)
                });
                pairs.push((max >> top, top));
            }
            let program = programs::arithmetic::cases(bits, op, &pairs);
            let prepared = TARGET
                .prepare(&program)
                .expect("a program this machine holds");
            assert_eq!(status(&prepared), 0, "{bits} {op:?}");
        }
    }
}

#[test]
fn runtime_monus_across_byte_boundaries() {
    for bits in [8, 9, 16, 32, 64] {
        if bits > TARGET.word() {
            continue;
        }
        let max = u64::MAX >> (64 - bits);
        let mut pairs = vec![
            (0, 0),
            (0, 1),
            (1, 0),
            (5, 5),
            (4, 5),
            (6, 5),
            (255, 256),
            (256, 255),
            (256, 256),
            (511, 256),
            (256, 1),
            (1, 256),
            (max, max),
            (max - 1, max),
            (max, max - 1),
            (max, 0),
            (0, max),
        ];
        pairs.retain(|&(left, right)| left <= max && right <= max);
        for chunk in pairs.chunks(8) {
            assert_eq!(
                status(&programs::arithmetic::cases(bits, Binary::Monus, chunk)),
                0,
                "{bits} {chunk:?}"
            );
        }
    }
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
    for op in [
        Binary::Mul,
        Binary::Div,
        Binary::Mod,
        Binary::And,
        Binary::Or,
        Binary::Xor,
    ] {
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
    let ladder = programs::ladder::every();
    assert_eq!(ladder.len(), LADDER_SIZES.len());
    let changed: Vec<_> = ladder
        .into_iter()
        .zip(LADDER_SIZES)
        .filter_map(|((name, barb), &(expected, size))| {
            assert_eq!(name, expected, "size baselines must match the ladder");
            let program = lowered(barb, &routines);
            let actual = TARGET
                .compile_machine_ir(&program)
                .expect("compilation")
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
    for (name, barb) in programs::ladder::every() {
        let program = lowered(barb, &routines);
        for (&argc, (status, stdout)) in COUNTS.iter().zip(execute_counts(&program, COUNTS)) {
            let said = if name == "a greeting" {
                "Hello, world!"
            } else {
                ""
            };
            assert_eq!(stdout, said, "{name}, argc={argc}");
            let answer = match name {
                "the count" => i32::from(argc),
                // Four past the count, and twice it, each keeping every bit
                // below the eighth and throwing the rest away.
                "the count and a constant" => i32::from(argc.wrapping_add(4) % 256),
                "the low bits of a sum" => i32::from(argc.wrapping_mul(2) % 256),
                // `a = n + 3`, `b = a + n`, then `a + b`.
                "a shared intermediate" if argc < 32 => 3 * i32::from(argc) + 6,
                "a constant" | "a shared intermediate" | "a greeting" => 0,
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
    faun_core::lower_to_machine_ir(&barb, routines).expect("a representable program")
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
