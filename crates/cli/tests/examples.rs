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
        ("(())", "part1: 0 part2: 0\n"),
        ("(()(()(", "part1: 3 part2: 0\n"),
        (")", "part1: -1 part2: 1\n"),
        ("()())", "part1: -1 part2: 5\n"),
        ("))(((((", "part1: 3 part2: 1\n"),
    ];
    for (input, expected) in cases {
        let (status, written) = support::run_file(&example("aoc/201501.fn"), input.as_bytes());
        assert_eq!((status, written.as_str()), (0, *expected), "{input}");
    }
}

/// Standard input to its end, then to standard output: what went, or the
/// error each step met, as its own status.
#[test]
fn streams_answer_what_they_moved_or_what_they_met() {
    let package = support::Package::new(
        "streams",
        "import std.host {Host IoError.*}

         main! : Host -> []
         main!(host) ->
           read = host.stdin.read_to_str!()
           text = read.ok_or(\"unreadable\")
           wrote = host.stdout.write_all!(text.to_utf8())
           host.exit!(status(wrote))

         status : Result(Nat IoError) -> Nat
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

/// A pure program run by the host: what it answers printed, an error it
/// answers reported, and each as its status.
#[test]
fn runners_print_what_a_program_answers_and_report_what_it_fails_with() {
    let answering = support::Package::new(
        "run",
        "import std.host {Host}

         answer : {} -> Nat
         answer(_) -> 42

         main! : Host -> []
         main!(host) -> host.run!(answer)",
    );
    assert_eq!(
        support::run_file(&answering.entry(), b""),
        (0, "42".to_owned())
    );

    let checking = support::Package::new(
        "run-result-text",
        "import std.host {Host}

         check : {stdin: Str} -> Result(Nat Str)
         check({stdin}) if stdin.len() > 3 -> Err(\"too long\")
         check({stdin}) -> Ok(stdin.len())

         main! : Host -> []
         main!(host) -> host.run_result_text!(check)",
    );
    assert_eq!(
        support::run_file(&checking.entry(), b"ab"),
        (0, "2".to_owned())
    );
    // The error goes to standard error, which this host drops.
    assert_eq!(
        support::run_file(&checking.entry(), b"abcd"),
        (1, String::new())
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
           greet!(host name)
           host.exit!(3)

         greet! : Host Str -> {}
         greet!(host name) ->
           host.println!(name)
           {}",
    );
    assert_eq!(
        support::run_file(&package.entry(), b""),
        (3, "Hello, world!\nHi, Faun\n".to_owned())
    );
}

/// Every program the README shows runs, and says what it says it does.
#[test]
fn the_readme_programs_run() {
    let readme =
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../README.md"))
            .unwrap();
    let programs: Vec<&str> = readme
        .split("```ruby\n")
        .skip(1)
        .map(|block| block.split("```").next().expect("a closed block"))
        .collect();
    let written = ["factorial(5) = 120\n", "Hello, world!\n"];
    assert_eq!(programs.len(), written.len());
    for (at, (program, written)) in programs.iter().zip(written).enumerate() {
        let package = support::Package::new(&format!("readme-{at}"), program);
        assert_eq!(
            support::run_file(&package.entry(), b""),
            (0, written.to_owned()),
            "{program}"
        );
    }
}
