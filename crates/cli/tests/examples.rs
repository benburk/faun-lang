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
