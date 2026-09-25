//! The language as Ori defines it, case by case: what a program answers, or
//! why it is refused.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
    (
        "a type nothing pins is Nat",
        "main! : Host -> []
         main!(host) -> host.exit!([].len() + [[] []].len())",
        2,
    ),
    (
        "a function, a constructor and a lambda are passed into calls",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         main! : Host -> []
         main!(host) ->
           doubled = [1 2].map(twice).fold(0 |s x| s + x)
           wrapped = [3].map(Ok).map(|r| r.ok_or(0)).fold(0 |s x| s + x)
           host.exit!(doubled + wrapped)",
        9,
    ),
];

/// Programs refused, and what the message says.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "a function is not bound",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         apply() ->
           f = twice
           f(1)",
        "cannot be bound",
    ),
    (
        "a function is not answered",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         pick : Bool -> (Nat -> Nat)
         pick(_) -> twice",
        "a function is passed into a call, never answered or stored",
    ),
    (
        "a function is not answered through a type variable",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         half : Nat -> Nat
         half(n) -> n / 2

         main! : Host -> []
         main!(host) -> host.exit!(True.select(twice half)(3))",
        "cannot be bound, answered, or stored",
    ),
    (
        "a function is not stored in data",
        "Handler : [Handler((Nat -> Nat))]",
        "constructor `Handler` holds a function",
    ),
    (
        "a definition with no parameters is reached with parentheses",
        "zero : Nat
         zero() -> 0

         apply : (Nat -> Nat) -> Nat
         apply(f) -> f(1)

         main! : Host -> []
         main!(host) -> host.exit!([zero].len())",
        "reached as `name()`",
    ),
];

#[test]
fn programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        assert_eq!(Package::new(name, source).run(), *expected, "{name}");
    }
}

#[test]
fn programs_are_refused_with_what_is_wrong() {
    for (name, source, expected) in REFUSED {
        let refused = Package::new(name, source).refusal();
        assert!(refused.contains(expected), "{name}: {refused}");
    }
}
