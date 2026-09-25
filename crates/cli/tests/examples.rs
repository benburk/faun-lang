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
