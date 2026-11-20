//! A list made only to be walked once, or only to be compared, is never
//! built: `List.range(n).fold(...)`, `List.repeat(x, n).sum()` and a walk
//! through `List.range(n).map(...)` cost what the loop written by hand
//! costs, and so does `key == [grey]`, which the comparison takes apart
//! where the caller made it, under either pipeline.
mod support;

use faun_core::targets::Pipeline;
use support::{Package, run_counted_through};

/// The fuel a program spends on `steps` bytes of input, which it takes as
/// how many steps to make, and what it prints.
fn spent(package: &Package, steps: usize, pipeline: Pipeline) -> (String, u64) {
    let (status, written, fuel) = run_counted_through(&package.entry(), &vec![0; steps], pipeline);
    assert_eq!(status, 0);
    (written.trim().to_owned(), fuel)
}

/// Both lowerings, each held to the same costs.
const PIPELINES: [Pipeline; 2] = [Pipeline::Stock, Pipeline::Lab];

/// What 100 steps more cost, a step.
fn per_step(package: &Package, pipeline: Pipeline) -> (String, u64) {
    let (_, first) = spent(package, 100, pipeline);
    let (printed, second) = spent(package, 200, pipeline);
    (printed, (second - first) / 100)
}

/// A program making `steps` steps, each of them `step(at, total)`, which
/// the definitions in `source` define, printing the total.
fn stepping(name: &str, source: &str) -> Package {
    Package::new(
        name,
        &format!(
            r#"
            {source}

            steps : (Nat, Nat, Nat) -> Nat
            steps(_, 0, total) -> total
            steps(at, Succ(left), total) -> steps(at + 1, left, step(at, total))

            app : {{stdin: List(U8), *}} -> Str
            app(input) -> "${{steps(0, input.stdin.len(), 0)}}"

            main!(host) -> host.run_stdin!(app)
            "#
        ),
    )
}

/// That the natural spelling of a step prints what the loop written by
/// hand prints, and costs no more than `slack` percent more a step.
fn as_cheap(name: &str, slack: u64, natural: &str, by_hand: &str) {
    let natural = stepping(name, natural);
    let by_hand = stepping(&format!("{name}-by-hand"), by_hand);
    for pipeline in PIPELINES {
        let (natural_printed, natural_step) = per_step(&natural, pipeline);
        let (hand_printed, hand_step) = per_step(&by_hand, pipeline);
        assert_eq!(natural_printed, hand_printed);
        assert!(
            natural_step * 100 <= hand_step * (100 + slack),
            "{pipeline:?}: a step cost {natural_step} fuel written naturally and {hand_step} by hand"
        );
    }
}

#[test]
fn a_range_folded_is_never_built() {
    as_cheap(
        "unbuilt-range-fold",
        2,
        r"
        step : (Nat, Nat) -> Nat
        step(at, total) -> List.range(48).fold(total, |sum, column| sum + column + at)
        ",
        r"
        columns : (Nat, Nat, Nat, Nat) -> Nat
        columns(_, _, 0, sum) -> sum
        columns(at, column, Succ(left), sum) -> columns(at, column + 1, left, sum + column + at)

        step : (Nat, Nat) -> Nat
        step(at, total) -> columns(at, 0, 48, total)
        ",
    );
}

/// A fold over a range whose step ignores the element counts its steps and
/// nothing else: the index the range would have handed it is never worked
/// out, so it costs what stepping `n.times` costs.
#[test]
fn a_range_folded_without_its_elements_costs_what_times_costs() {
    as_cheap(
        "unbuilt-range-unread",
        0,
        r"
        step : (Nat, Nat) -> Nat
        step(at, total) -> List.range(48).fold(total, |sum, _| (sum * 3 + at) % 1000003)
        ",
        r"
        step : (Nat, Nat) -> Nat
        step(at, total) -> 48.times(total, |sum| (sum * 3 + at) % 1000003)
        ",
    );
}

/// A program printing `fib` of a number it reads from its input, its bytes
/// as the digits of a number base 256 and their count added, so nothing
/// bounds it: as many zero bytes, that many.
fn reading(name: &str, source: &str) -> Package {
    Package::new(
        name,
        &format!(
            r#"
            {source}

            app : {{stdin: List(U8), *}} -> Str
            app(input) -> (
              read = input.stdin.fold(0, |n, byte| n * 256 + byte.to_nat())
              "${{fib(read + input.stdin.len())}}"
            )

            main!(host) -> host.run_stdin!(app)
            "#
        ),
    )
}

/// A count taken one from where a pattern has already found it a step
/// costs what the step's own predecessor does, as `n.times` reads it.
#[test]
fn a_count_taken_one_from_costs_what_times_costs() {
    let natural = reading(
        "unbuilt-count-down",
        r"
        down : (Nat, Nat, Nat) -> Nat
        down(0, a, _) -> a
        down(k, a, b) -> down(k - 1, b, (a + b) % 1000003)

        fib : Nat -> Nat
        fib(n) -> down(n, 0, 1)
        ",
    );
    let times = reading(
        "unbuilt-count-times",
        r"
        fib : Nat -> Nat
        fib(n) -> (
          (a, _) = n.times((0, 1), |(a, b)| (b, (a + b) % 1000003))
          a
        )
        ",
    );
    for pipeline in PIPELINES {
        let (natural_printed, natural_step) = per_step(&natural, pipeline);
        let (times_printed, times_step) = per_step(&times, pipeline);
        assert_eq!(natural_printed, times_printed);
        assert!(
            natural_step <= times_step,
            "{pipeline:?}: a step cost {natural_step} fuel counted down and {times_step} with times"
        );
    }
}

#[test]
fn a_repeat_summed_is_never_built() {
    as_cheap(
        "unbuilt-repeat",
        2,
        r"
        step : (Nat, Nat) -> Nat
        step(at, total) -> total + List.repeat(at % 5, 48).sum()
        ",
        r"
        repeated : (Nat, Nat, Nat) -> Nat
        repeated(_, 0, sum) -> sum
        repeated(value, Succ(left), sum) -> repeated(value, left, sum + value)

        step : (Nat, Nat) -> Nat
        step(at, total) -> total + repeated(at % 5, 48, 0)
        ",
    );
}

#[test]
fn a_range_filtered_and_mapped_through_recursion_is_never_built() {
    // Queens: each column a queen can stand in, the ways to fill the rows
    // after it summed, which walks a range again for every queen placed.
    as_cheap(
        "unbuilt-queens",
        20,
        r"
        clear : (Nat, List(Nat), Nat) -> Bool
        clear(_, [], _) -> True
        clear(column, [queen, *_], distance) if queen == column | queen + distance == column | column + distance == queen -> False
        clear(column, [_, *queens], distance) -> clear(column, queens, distance + 1)

        ways : (Nat, Nat, List(Nat)) -> Nat
        ways(_, 0, _) -> 1
        ways(size, rows, queens) -> List.range(size)
          .filter(|column| clear(column, queens, 1))
          .map(|column| ways(size, rows - 1, [column, *queens]))
          .sum()

        step : (Nat, Nat) -> Nat
        step(at, total) -> total + ways(4 + at % 2, 4 + at % 2, [])
        ",
        r"
        clear : (Nat, List(Nat), Nat) -> Bool
        clear(_, [], _) -> True
        clear(column, [queen, *_], distance) if queen == column | queen + distance == column | column + distance == queen -> False
        clear(column, [_, *queens], distance) -> clear(column, queens, distance + 1)

        columns : (Nat, Nat, Nat, List(Nat), Nat) -> Nat
        columns(size, column, rows, queens, sum) -> (
          if column >= size return sum
          more = if clear(column, queens, 1) then ways(size, rows - 1, [column, *queens]) else 0
          columns(size, column + 1, rows, queens, sum + more)
        )

        ways : (Nat, Nat, List(Nat)) -> Nat
        ways(_, 0, _) -> 1
        ways(size, rows, queens) -> columns(size, 0, rows, queens, 0)

        step : (Nat, Nat) -> Nat
        step(at, total) -> total + ways(4 + at % 2, 4 + at % 2, [])
        ",
    );
}

#[test]
fn a_list_literal_compared_is_never_built() {
    // PNG's tRNS: a grey sample hidden where it is the key's one element.
    as_cheap(
        "unbuilt-literal",
        5,
        r"
        key : Nat -> List(Nat)
        key(at) -> if at % 3 == 0 then [] else [at % 5]

        step : (Nat, Nat) -> Nat
        step(at, total) -> if key(at / 3) == [at % 5] then total + 1 else total
        ",
        r"
        key : Nat -> List(Nat)
        key(at) -> if at % 3 == 0 then [] else [at % 5]

        step : (Nat, Nat) -> Nat
        step(at, total) -> if key(at / 3) is (
          [k] then k == at % 5
          _ then False
        ) then total + 1 else total
        ",
    );
}

#[test]
fn a_longer_literal_compared_is_taken_apart_an_element_at_a_time() {
    // And an RGB sample, three elements against three.
    as_cheap(
        "unbuilt-literal-rgb",
        2,
        r"
        key : Nat -> List(Nat)
        key(at) -> if at % 4 == 0 then [] else [at % 2, at % 3, at % 5]

        step : (Nat, Nat) -> Nat
        step(at, total) -> if key(at) == [at % 2, (at / 2) % 3, at % 5] then total + 1 else total
        ",
        r"
        key : Nat -> List(Nat)
        key(at) -> if at % 4 == 0 then [] else [at % 2, at % 3, at % 5]

        step : (Nat, Nat) -> Nat
        step(at, total) -> if key(at) is (
          [r, g, b] then r == at % 2 & g == (at / 2) % 3 & b == at % 5
          _ then False
        ) then total + 1 else total
        ",
    );
}

#[test]
fn a_range_mapped_and_read_by_position_is_never_built() {
    // Each element read once, by `get` at a position counted up, and two
    // positions past the end, which find nothing there as they would in
    // the list built.
    as_cheap(
        "unbuilt-positions",
        5,
        r"
        indexed : (List(Nat), Nat, Nat) -> Nat
        indexed(xs, i, sum) -> (
          if i >= xs.len() + 2 return sum
          indexed(xs, i + 1, sum + xs.get(i).ok_or(7))
        )

        step : (Nat, Nat) -> Nat
        step(at, total) -> indexed(List.range(48).map(|column| column * 3 + at), 0, total)
        ",
        r"
        columns : (Nat, Nat, Nat, Nat) -> Nat
        columns(_, _, 0, sum) -> sum + 14
        columns(at, column, Succ(left), sum) -> columns(at, column + 1, left, sum + column * 3 + at)

        step : (Nat, Nat) -> Nat
        step(at, total) -> columns(at, 0, 48, total)
        ",
    );
}
