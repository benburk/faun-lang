//! Shared executable fixtures written in the simple source language.

use faun::ir::Program;

/// A program read from text, against what a compiler knows.
fn read(text: &str) -> Program {
    crate::read(text, &faun::platform::Routines::builtin())
        .unwrap_or_else(|error| panic!("{error}\n{text}"))
}

/// Every program here and what it leaves with.
///
/// What a program answers is a fact about the program, so it is said here
/// rather than once per machine. A target is handed all of them and has to
/// answer the same as every other, which is the whole of what it means for
/// two targets to agree.
#[must_use]
pub fn running() -> Vec<(&'static str, Program, i32)> {
    let mut held = answers_built();
    held.extend(answers_written());
    held.extend(answers_counted());
    held.extend(answers_leaving());
    held.extend(answers_tagged());
    held.extend(arithmetic_cases());
    held.push(("a runtime guard exits early", rejected_count(), 7));
    held
}

fn answers_built() -> Vec<(&'static str, Program, i32)> {
    vec![
        ("two and two", faun::programs::two_and_two(), 4),
        (
            "a long arm first",
            faun::programs::a_branch_over_a_long_arm(40, true),
            40,
        ),
        (
            "a long arm last",
            faun::programs::a_branch_over_a_long_arm(40, false),
            40,
        ),
        ("a global", faun::programs::counts_in_a_global(), 3),
        ("eight bits", faun::programs::wraps_at_eight_bits(), 4),
        (
            "values across a call",
            faun::programs::values_survive_a_call(),
            45,
        ),
        (
            "a comparison",
            faun::programs::compares_two_worked_out_values(),
            1,
        ),
        (
            "a flag it read",
            faun::programs::branches_on_a_flag_it_read(),
            7,
        ),
        (
            "a total into an arm",
            faun::programs::carries_a_total_into_an_arm(3),
            3,
        ),
    ]
}

/// And the ones written, which are what it does.
fn answers_written() -> Vec<(&'static str, Program, i32)> {
    vec![
        (
            "exit zero",
            read(
                "type Nat Zero Succ(Nat)

                  main!(h) -> exit!(h Zero)",
            ),
            0,
        ),
        (
            "a status it was told",
            read(
                "type Nat Zero Succ(Nat)

                  main!(h) -> exit!(h Succ(Succ(Succ(Zero))))",
            ),
            3,
        ),
        (
            "a name that leaves",
            read(
                "type Nat Zero Succ(Nat)

                  die!(h n) -> exit!(h n)

                  main!(h) -> die!(h Succ(Succ(Zero)))",
            ),
            2,
        ),
        (
            "a tag from a count",
            read(
                "type Nat Succ(Nat) Zero
                  type Bool True False

                  count(False) -> Zero
                  count(True) -> Succ(Zero)

                  main!(h) -> exit!(h count(True))",
            ),
            1,
        ),
    ]
}

/// The rest of them, arithmetic and what the world handed over.
fn answers_counted() -> Vec<(&'static str, Program, i32)> {
    vec![
        (
            "how many arguments",
            read(
                "type Nat Zero Succ(Nat)

                  add(a Zero) -> a
                  add(a Succ(k)) -> Succ(add(a k))

                  type Bool False True
                  less_than(Zero Zero) -> False
                  less_than(Zero Succ(b)) -> True
                  less_than(Succ(a) Zero) -> False
                  less_than(Succ(a) Succ(b)) -> less_than(a b)
                  bounded!(h True n) -> n
                  bounded!(h False n) -> exit!(h Zero)

                  main!(h) ->
                    count = argc!(h)
                    n = bounded!(h less_than(count Succ(Succ(Zero))) count)
                    exit!(h add(n n))",
            ),
            2,
        ),
        (
            "two and two from text",
            read(
                "type Nat Zero Succ(Nat)

                  add(a Zero) -> a
                  add(a Succ(k)) -> Succ(add(a k))

                  main!(h) -> exit!(h add(Succ(Succ(Zero)) Succ(Succ(Zero))))",
            ),
            4,
        ),
    ]
}

/// An arm that leaves, reached and not reached. What the other arms answer
/// is not measured against one that never comes back.
fn answers_leaving() -> Vec<(&'static str, Program, i32)> {
    let mut held = Vec::new();
    let leaving = "type Nat Zero Succ(Nat)

                   pick!(h Zero) -> exit!(h Succ(Zero))
                   pick!(h Succ(k)) -> k

                   main!(h) ->
                     held = pick!(h WHICH)
                     exit!(h Succ(held))";
    held.push((
        "an arm that comes back",
        read(&leaving.replace("WHICH", "Succ(Succ(Zero))")),
        2,
    ));
    held.push((
        "an arm that leaves",
        read(&leaving.replace("WHICH", "Zero")),
        1,
    ));
    held
}

/// A tag read back as the constructor it is, and two columns matched at
/// once. Subtraction stops at nought rather than wrapping, which is what
/// the second column buys: the arm for `Succ(m) Zero` is the one saying so.
fn answers_tagged() -> Vec<(&'static str, Program, i32)> {
    let mut held = Vec::new();
    let ordering = "type Nat Zero Succ(Nat)
                    type Order Lt Eq Gt

                    rank(Lt) -> Zero
                    rank(Eq) -> Succ(Zero)
                    rank(Gt) -> Succ(Succ(Zero))

                    pick(Zero) -> Lt
                    pick(Succ(k)) -> Gt

                    main!(h) -> exit!(h rank(pick(WHICH)))";
    for (which, answer) in [("Zero", 0), ("Succ(Zero)", 2)] {
        held.push(("a tag", read(&ordering.replace("WHICH", which)), answer));
    }

    let arithmetic = "type Nat Zero Succ(Nat)
                      type Order Lt Eq Gt

                      sub(Zero b) -> Zero
                      sub(Succ(m) Zero) -> Succ(m)
                      sub(Succ(m) Succ(n)) -> sub(m n)

                      cmp(Zero Zero) -> Eq
                      cmp(Zero Succ(n)) -> Lt
                      cmp(Succ(m) Zero) -> Gt
                      cmp(Succ(m) Succ(n)) -> cmp(m n)

                      rank(Lt) -> Zero
                      rank(Eq) -> Succ(Zero)
                      rank(Gt) -> Succ(Succ(Zero))

                      three(n) -> Succ(Succ(Succ(n)))

                      main!(h) -> exit!(h ANSWER)";
    for (answer, want) in [
        ("sub(three(Zero) Succ(Zero))", 2),
        ("sub(Succ(Zero) three(Zero))", 0),
        ("rank(cmp(Succ(Zero) three(Zero)))", 0),
        ("rank(cmp(three(Zero) three(Zero)))", 1),
        ("rank(cmp(three(Zero) Succ(Zero)))", 2),
    ] {
        held.push((
            "two columns",
            read(&arithmetic.replace("ANSWER", answer)),
            want,
        ));
    }
    held
}

fn rejected_count() -> Program {
    let library = include_str!("../standard/nat.fn");
    let source = format!(
        "{library}\n
        bounded!(h True n) -> n
        bounded!(h False n) -> exit!(h Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))))
        main!(h) ->
            count = argc!(h)
            n = bounded!(h less_than(count Succ(Zero)) count)
            exit!(h n)"
    );
    read(&source)
}

/// Runtime arithmetic: the count cannot fold, and the guard is what makes
/// its subsequent arithmetic fit even on the smallest target.
#[must_use]
pub fn arithmetic_cases() -> Vec<(&'static str, Program, i32)> {
    let library = include_str!("../standard/nat.fn");
    let setup = "
        bounded!(h True n) -> n
        bounded!(h False n) -> exit!(h Zero)
        four(n) -> Succ(Succ(Succ(Succ(n))))
        rank(False) -> Zero
        rank(True) -> Succ(Zero)
        main!(h) ->
            count = argc!(h)
            n = bounded!(h less_than(count Succ(Succ(Zero))) count)
            a = add(n four(four(Zero)))
            b = Succ(n)
            z = sub(n n)
            exit!(h ANSWER)";
    [
        ("runtime addition", "add(a b)", 11),
        ("runtime monus", "sub(a b)", 7),
        ("runtime underflow", "sub(b a)", 0),
        ("runtime multiplication", "mul(a b)", 18),
        ("runtime division", "div(a b)", 4),
        ("runtime remainder", "mod(a b)", 1),
        ("runtime division by zero", "div(a z)", 0),
        ("runtime remainder by zero", "mod(a z)", 9),
        ("runtime less than", "rank(less_than(b a))", 1),
        ("runtime equality", "rank(equals(a a))", 1),
        ("runtime inequality", "rank(equals(a b))", 0),
    ]
    .into_iter()
    .map(|(name, answer, want)| {
        let source = format!("{library}\n{}", setup.replace("ANSWER", answer));
        (name, read(&source), want)
    })
    .collect()
}
