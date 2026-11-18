//! A natural a loop carries is a machine word wherever its range is proven
//! to fit one, and exact everywhere else: a position stepped under a guard
//! comparing it with a list's length, and a count below a constant joined
//! to another test by `&`, cost what the same loop over `U64` costs, while
//! a natural whose guard is no length crosses every word width and stays
//! the number it is, on every target and backend.
mod support;

use std::process::Command;
use support::{Package, run_counted};

/// The fuel a program spends on `steps` bytes of input, and what it prints.
fn spent(package: &Package, steps: usize) -> (String, u64) {
    let input: Vec<u8> = (0..steps)
        .map(|at| u8::try_from(at * 7 % 13).unwrap())
        .collect();
    let (status, written, fuel) = run_counted(&package.entry(), &input);
    assert_eq!(status, 0);
    (written.trim().to_owned(), fuel)
}

/// What 100 bytes of input more cost, a byte.
fn per_byte(package: &Package) -> (String, u64) {
    let (_, first) = spent(package, 200);
    let (printed, second) = spent(package, 300);
    (printed, (second - first) / 100)
}

/// A program printing `walk(input.stdin)`, which `source` defines.
fn walking(name: &str, source: &str) -> Package {
    Package::new(
        name,
        &format!(
            r#"
            {source}

            app : {{stdin: List(U8), *}} -> Str
            app(input) -> "${{walk(input.stdin)}}"

            main!(host) -> host.run_stdin!(app)
            "#
        ),
    )
}

/// That the natural spelling prints what the workaround over `U64` prints,
/// and costs no more than `slack` percent more a byte.
fn as_cheap(name: &str, slack: u64, natural: &str, workaround: &str) {
    let (natural_printed, natural_byte) = per_byte(&walking(name, natural));
    let (hand_printed, hand_byte) = per_byte(&walking(&format!("{name}-u64"), workaround));
    assert_eq!(natural_printed, hand_printed);
    assert!(
        natural_byte * 100 <= hand_byte * (100 + slack),
        "a byte cost {natural_byte} fuel written naturally and {hand_byte} over U64"
    );
}

#[test]
fn a_position_below_a_length_is_a_word() {
    // `at + 2 < input.len()` bounds `at` itself, and the walk hands `at + 1`
    // on only there, so every position is below the length.
    as_cheap(
        "guarded-position",
        3,
        r"
        step : (List(U8), Nat, Nat) -> Nat
        step(input, at, total) -> (
          if at + 2 >= input.len() return total
          step(input, at + 1, total + input.get(at).ok_or(0).to_nat() + input.get(at + 2).ok_or(0).to_nat())
        )

        walk : List(U8) -> Nat
        walk(input) -> step(input, 0, 0)
        ",
        r"
        step : (List(U8), U64, Nat) -> Nat
        step(input, at, total) -> (
          if (at + 2).to_nat() >= input.len() return total
          step(input, at + 1, total + input.get(at.to_nat()).ok_or(0).to_nat() + input.get((at + 2).to_nat()).ok_or(0).to_nat())
        )

        walk : List(U8) -> Nat
        walk(input) -> step(input, U64.of_nat(0), 0)
        ",
    );
}

#[test]
fn a_count_below_a_constant_joined_by_and_is_a_word() {
    // `count < 16 & ...` is a `Bool` worked out by a match: its `True` says
    // the first comparison held, so the count handed on is below 17.
    as_cheap(
        "guarded-count",
        3,
        r"
        agree : (List(U8), Nat, Nat) -> Nat
        agree(input, at, count) if count < 16 & input.get(at + count).ok_or(0) == input.get(count).ok_or(0) ->
          agree(input, at, count + 1)
        agree(_, _, count) -> count

        step : (List(U8), Nat, Nat) -> Nat
        step(input, at, total) -> (
          if at >= input.len() return total
          step(input, at + 1, total + agree(input, at, 0))
        )

        walk : List(U8) -> Nat
        walk(input) -> step(input, 0, 0)
        ",
        r"
        agree : (List(U8), Nat, U64) -> U64
        agree(input, at, count) if count < 16 & input.get(at + count.to_nat()).ok_or(0) == input.get(count.to_nat()).ok_or(0) ->
          agree(input, at, count + 1)
        agree(_, _, count) -> count

        step : (List(U8), Nat, Nat) -> Nat
        step(input, at, total) -> (
          if at >= input.len() return total
          step(input, at + 1, total + agree(input, at, U64.of_nat(0)).to_nat())
        )

        walk : List(U8) -> Nat
        walk(input) -> step(input, 0, 0)
        ",
    );
}

/// Every target and backend `faun run` builds for.
const MACHINES: [(&str, &str); 6] = [
    ("x86_64-linux", "stock"),
    ("x86_64-linux", "lab"),
    ("wasm32-wasi", "stock"),
    ("wasm32-wasi", "lab"),
    ("mos6502-sim65", "stock"),
    ("mos6502-sim65", "lab"),
];

/// That `package` prints `expected` built for every target and backend.
fn prints_everywhere(package: &Package, expected: &str) {
    for (target, backend) in MACHINES {
        let result = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(["run", "--backend", backend, "--target", target])
            .arg(package.entry())
            .output()
            .unwrap();
        assert_eq!(
            (
                result.status.code(),
                String::from_utf8_lossy(&result.stdout).trim()
            ),
            (Some(0), expected),
            "{target} {backend}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

/// The sum `walk` prints from `start` stepping by `step` while below
/// `limit`, and its last position, worked out as the program should.
fn stepped(start: u128, step: u128, limit: u128) -> String {
    let (mut at, mut sum, mut last) = (start, 0u128, start);
    while at + step <= limit {
        sum += at;
        last = at;
        at += step;
    }
    format!("{sum} {last}")
}

#[test]
fn a_natural_guarded_by_no_length_crosses_every_word_exactly() {
    // The limit is no list's length, so nothing bounds the position but the
    // natural it is: each walk starts a few steps below a word's top and
    // goes past it, which a position held in a word would wrap.
    let package = Package::new(
        "crossing-words",
        r#"
        walk : (Nat, Nat, Nat, Nat) -> Str
        walk(at, limit, sum, last) -> (
          if at + 3 > limit return "${sum} ${last}"
          walk(at + 3, limit, sum + at, at)
        )

        main!(host) -> (
          lift = host.args.len()
          lines = [16, 32, 64].map(|bits| walk(2.pow(bits) - 7 + lift, 2.pow(bits) + 8, 0, 0))
          printed = host.println!(lines.join(" | "))
          host.exit!(0)
        )
        "#,
    );
    let expected: Vec<String> = [16u32, 32, 64]
        .iter()
        .map(|&bits| stepped((1u128 << bits) - 7 + 1, 3, (1u128 << bits) + 8))
        .collect();
    prints_everywhere(&package, &expected.join(" | "));
}
