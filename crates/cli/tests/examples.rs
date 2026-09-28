//! The example programs, run on the reference interpreter with the input
//! each is written for.

mod support;

use std::path::PathBuf;

fn example(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../faun/examples")
        .join(name)
}

#[test]
fn advent_of_code_2015_day_one_answers_the_puzzle_examples() {
    let cases: &[(&str, &str)] = &[
        ("(())", "Ok({part1: 0, part2: 0})\n"),
        ("(()(()(", "Ok({part1: 3, part2: 0})\n"),
        (")", "Ok({part1: -1, part2: 1})\n"),
        ("()())", "Ok({part1: -1, part2: 5})\n"),
        ("))(((((", "Ok({part1: 3, part2: 1})\n"),
    ];
    for (input, expected) in cases {
        let (status, written) = support::run_file(&example("aoc/201501.fn"), input.as_bytes());
        assert_eq!((status, written.as_str()), (0, *expected), "{input}");
    }
}

/// Hello, world, written once from where it lies; how small that is, is
/// held by the ladder's greeting.
#[test]
fn minimal_hello_says_hello() {
    assert_eq!(
        support::run_file(&example("minimal-hello.fn"), b""),
        (0, "Hello, world!".to_owned())
    );
}

/// Standard input to its end, then to standard output: what went, or the
/// error each step met, as its own status.
#[test]
fn streams_answer_what_they_moved_or_what_they_met() {
    let package = support::Package::new(
        "streams",
        "import std.host {Host, IoError.*}

         main! : Host -> []
         main!(host) ->
           read = host.stdin.read_to_str!()
           text = read.ok_or(\"unreadable\")
           wrote = host.stdout.write_all!(text.to_utf8())
           host.exit!(status(wrote))

         status : Result(Nat, IoError) -> Nat
         status(Ok(n)) -> n % 100
         status(Err(BrokenPipe)) -> 101
         status(Err(NoSpace)) -> 102
         status(Err(_)) -> 103",
    );
    let long = "ab".repeat(700);
    assert_eq!(
        support::run_file(&package.entry(), long.as_bytes()),
        (1400 % 100, long.clone())
    );
    // Not UTF-8, so not read as text.
    assert_eq!(
        support::run_file(&package.entry(), &[0x66, 0xC0, 0x80]),
        (10, "unreadable".to_owned())
    );
    // Linux's EPIPE and ENOSPC, as the host module reads them.
    for (errno, status) in [(32, 101), (28, 102), (5, 103)] {
        assert_eq!(
            support::run_failing(&package.entry(), b"x", Some(errno)).0,
            status
        );
    }
}

/// A pure program run by the host: what it answers printed and a line's
/// end, a `Result` saying which it was, and status nought either way. An
/// app reads the fields it declares, and the rest are handed all the same.
#[test]
fn runners_print_what_a_program_answers() {
    let answering = support::Package::new(
        "run",
        "import std.host {Host}

         answer : {args: List(Str), *} -> Nat
         answer(_) -> 42

         main! : Host -> []
         main!(host) -> host.run!(answer)",
    );
    assert_eq!(
        support::run_file(&answering.entry(), b""),
        (0, "42\n".to_owned())
    );

    let checking = support::Package::new(
        "run-stdin",
        "import std.host {Host}

         check : {stdin: List(U8), *} -> Result(Nat, Str)
         check({stdin, *}) if stdin.len() > 3 -> Err(\"too long\")
         check({stdin, *}) -> Ok(stdin.len())

         main! : Host -> []
         main!(host) -> host.run_stdin!(check)",
    );
    assert_eq!(
        support::run_file(&checking.entry(), b"ab"),
        (0, "Ok(2)\n".to_owned())
    );
    assert_eq!(
        support::run_file(&checking.entry(), b"abcd"),
        (0, "Err(too long)\n".to_owned())
    );
}

/// An effect on a line of its own is asked for what it does, and its answer
/// is not kept; the line after it goes on, and the next clause is its own.
#[test]
fn an_effect_on_its_own_line_goes_on_to_the_next() {
    let package = support::Package::new(
        "statements",
        "main! : Host -> []
         main!(host) ->
           host.println!(\"Hello, world!\")
           name = \"Faun\"
           host.print!(\"Hi, \")
           greet!(host, name)
           host.exit!(3)

         greet! : (Host, Str) -> {}
         greet!(host, name) ->
           host.println!(name)
           {}",
    );
    assert_eq!(
        support::run_file(&package.entry(), b""),
        (3, "Hello, world!\nHi, Faun\n".to_owned())
    );
}

/// A runner handed the arguments: what the program answers of them printed.
/// The reference interpreter holds no arguments to read, so this runs the
/// program on the machine.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn argument_runners_hand_the_program_its_arguments() {
    let run = |package: &support::Package, args: &[&str]| {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_faun"))
            .arg("run")
            .arg(package.entry())
            .arg("--")
            .args(args)
            .output()
            .unwrap();
        (
            output.status.code(),
            String::from_utf8(output.stdout).unwrap(),
        )
    };
    let counting = support::Package::new(
        "run-args",
        "count : {args: List(Str)} -> Nat
         count({args}) -> args.len()

         main!(host) -> host.run!(count)",
    );
    assert_eq!(run(&counting, &["a", "b"]), (Some(0), "3\n".to_owned()));

    let second = support::Package::new(
        "run-result-args",
        "second : {args: List(Str)} -> Result(Str, [OutOfBounds])
         second({args}) -> args.get(1)

         main!(host) -> host.run!(second)",
    );
    assert_eq!(
        run(&second, &["hello"]),
        (Some(0), "Ok(hello)\n".to_owned())
    );
    assert_eq!(
        run(&second, &[]),
        (Some(0), "Err(OutOfBounds)\n".to_owned())
    );
}

/// The standard-input runner reads the input to its end and hands it to the
/// program beside the arguments.
#[test]
fn the_stdin_runner_hands_the_program_arguments_and_input() {
    let run = |package: &support::Package, args: &[&str], input: &str| {
        let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_faun"))
            .arg("run")
            .arg(package.entry())
            .arg("--")
            .args(args)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        std::io::Write::write_all(&mut child.stdin.take().unwrap(), input.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        (
            output.status.code(),
            String::from_utf8(output.stdout).unwrap(),
        )
    };
    let both = support::Package::new(
        "run-input",
        "both : {args: List(Str), stdin: List(U8)} -> Str
         both({args, stdin}) ->
           text = Str.from_utf8(stdin).ok_or(\"\")
           \"${args.len()} ${text}\"

         main!(host) -> host.run_stdin!(both)",
    );
    assert_eq!(run(&both, &["a"], "in"), (Some(0), "2 in\n".to_owned()));
    let named = support::Package::new(
        "run-result-input",
        "named : {args: List(Str), stdin: List(U8)} -> Result(Str, [OutOfBounds])
         named({args, stdin}) ->
           name = args.get(1)?
           text = Str.from_utf8(stdin).ok_or(\"\")
           Ok(\"${name}: ${text}\")

         main!(host) -> host.run_stdin!(named)",
    );
    assert_eq!(run(&named, &["x"], "y"), (Some(0), "Ok(x: y)\n".to_owned()));
    assert_eq!(
        run(&named, &[], "y"),
        (Some(0), "Err(OutOfBounds)\n".to_owned())
    );
}

/// Ori's Advent of Code programs and example libraries, ported: every
/// expectation each file's package holds.
#[test]
fn the_ported_programs_and_libraries_hold() {
    let mut files = Vec::new();
    let mut pending = vec![example("aoc"), example("libraries")];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|extension| extension == "fn") {
                files.push(path);
            }
        }
    }
    files.sort();
    assert!(files.len() >= 40, "{files:?}");
    // Each file is its own program, and together they are most of the
    // suite's time: run on one thread, the slowest waits on all the rest.
    std::thread::scope(|scope| {
        let runs: Vec<_> = files
            .iter()
            .map(|file| (file, scope.spawn(|| support::test_file(file))))
            .collect();
        for (file, run) in runs {
            let (failed, _) = run
                .join()
                .unwrap_or_else(|_| panic!("{} panicked", file.display()));
            assert_eq!(failed, Vec::<String>::new(), "{}", file.display());
        }
    });
}

/// The grammar, construct by construct: every expectation of the syntax
/// examples holds.
#[test]
fn the_syntax_examples_hold() {
    let (failed, count) = support::test_file(&example("syntax/main.fn"));
    assert_eq!(failed, Vec::<String>::new());
    assert_eq!(count, 93);
}

/// The n-body benchmark's energies, after nought, one and ten steps, are
/// the ones the benchmarks game gives: built and run on this machine as
/// `faun test` does, since its floats are the machine's own.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn the_nbody_example_holds() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_faun"))
        .arg("test")
        .arg(example("nbody/main.fn"))
        .output()
        .unwrap();
    let said = String::from_utf8(output.stdout).unwrap();
    assert!(output.status.success(), "{said}");
    assert_eq!(said, "3 expectations hold\n");
}

/// What opening a file meets, as Linux says it: nothing there, something
/// there already, and a name reaching above where the program runs. A
/// write goes where the file was opened to write it.
#[test]
fn files_answer_what_opening_one_met() {
    let package = support::Package::new(
        "files",
        "import std.host {Files, File, IoError.*, Mode.*}

         main! : Host -> []
         main!(host) ->
           status = met!(host.files)
           host.exit!(status)

         met! : Files -> Nat
         met!(files) ->
           missing = files.open!(\"missing.txt\", Read)
           again = files.open!(\"here.txt\", CreateNew)
           above = files.open!(\"../above.txt\", Read)
           kept = files.open!(\"here.txt\", Append)
           said!(missing, again, above, kept)

         said! : (Result(File, IoError), Result(File, IoError), Result(File, IoError), Result(File, IoError)) -> Nat
         said!(Err(NotFound), Err(AlreadyExists), Err(Escapes), Ok(file)) ->
           wrote = file.write_all!(\"!\".to_utf8())
           closed = file.close!()
           0
         said!(missing, again, above, kept) ->
           a = close_any!(missing)
           b = close_any!(again)
           c = close_any!(above)
           d = close_any!(kept)
           1

         close_any! : Result(File, IoError) -> Nat
         close_any!(Ok(file)) ->
           closed = file.close!()
           0
         close_any!(Err(_)) -> 0",
    );
    let files = [("here.txt".to_owned(), b"there".to_vec())].into();
    let (status, _, left) = support::run_among(&package.entry(), files);
    assert_eq!(status, 0);
    assert_eq!(left["here.txt"], b"there!");
}

/// Appending writes after a list's end where nothing else holds its
/// buffer, and otherwise grows it with room after: twenty thousand appends
/// are linear work, which a copy per append would not finish.
#[test]
fn appends_are_linear_work() {
    let package = support::Package::new(
        "appends",
        "built : (Nat, List(Nat)) -> List(Nat)
         built(0, values) -> values
         built(Succ(n), values) -> built(n, values.append(n % 7))

         main! : Host -> []
         main!(host) ->
           values = built(20000, [])
           host.exit!(values.len() % 256 + values.get_or(19999, 9))",
    );
    assert_eq!(package.run(), 20000 % 256);
}
