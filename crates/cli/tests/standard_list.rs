//! The standard list answers what Ori's does. Each case is a Faun program
//! lowered for x86-64 and run on the reference interpreter, so what it
//! checks is the library and the tiers above a target, whatever any one
//! backend can yet hold: lists of lists, and counts with no bound.

mod support;

use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;
use support::Package;

/// Each case: what it exercises, the status it exits with, and what it
/// leaves with from `xs`, `[0, 1, 2, 3, 4]`, and `n`, its length.
const CASES: &[(&str, &str, u32)] = &[
    ("len", "xs.len() + xs.take(0).len()", 5),
    (
        "is_empty",
        "xs.is_empty().to_nat() + xs.take(0).is_empty().to_nat() * 2",
        2,
    ),
    ("append", "xs.append(9).get_or(5, 0)", 9),
    (
        "concat",
        "xs.concat([7, 8]).get_or(6, 0) + xs.concat([7, 8]).len() * 10",
        78,
    ),
    (
        "prepend",
        "xs.prepend(9).get_or(0, 0) + xs.prepend(9).len() * 10",
        69,
    ),
    ("map", "xs.map(|x| x * 2).get_or(4, 0)", 8),
    (
        "map2",
        "xs.map2([10, 20], |a, b| a + b).fold(0, |s, x| s + x)",
        31,
    ),
    ("flat_map", "xs.flat_map(|x| [x, x]).len()", 10),
    ("flatten", "[[1, 2], [], [3]].flatten().len()", 3),
    (
        "join",
        "[[1], [2, 3], [4]].join([0, 0]).len() + [[7]].join([0]).len() * 10",
        18,
    ),
    (
        "filter",
        "xs.filter(|x| x % 2 == 1).fold(0, |s, x| s + x)",
        4,
    ),
    ("count", "xs.count(|x| x % 2 == 0)", 3),
    (
        "any",
        "xs.any(|x| x == 2).to_nat() + xs.any(|x| x == 9).to_nat() * 2",
        1,
    ),
    (
        "all",
        "[1, 3].all(|x| x % 2 == 1).to_nat() + xs.all(|x| x % 2 == 1).to_nat() * 2",
        1,
    ),
    ("fold", "xs.fold(0, |s, x| s * 10 + x)", 1_234 % 256),
    (
        "fold_right",
        "xs.fold_right(0, |x, s| s * 10 + x)",
        43_210 % 256,
    ),
    (
        "trail",
        "xs.trail(0, |s, x| s + x).get_or(4, 0) + xs.trail(0, |s, x| s + x).len() * 20",
        110,
    ),
    (
        "reverse",
        "xs.reverse().get_or(0, 9) + xs.reverse().len() * 10",
        54,
    ),
    (
        "first",
        "xs.first().ok_or(9) + xs.take(0).first().ok_or(9) * 10",
        90,
    ),
    (
        "last",
        "xs.last().ok_or(9) + xs.take(0).last().ok_or(9) * 10",
        94,
    ),
    ("get", "xs.get(3).ok_or(9) + xs.get(n).ok_or(9) * 10", 93),
    ("get_or", "xs.get_or(2, 9) + xs.get_or(n, 9) * 10", 92),
    (
        "put",
        "xs.put(1, 7).get_or(1, 0) + xs.put(n, 7).len() * 10 + xs.put(n, 7).get_or(4, 0) * 100",
        (7 + 50 + 400) % 256,
    ),
    (
        "set",
        "xs.set(1, 7).ok_or([]).get_or(1, 0) + xs.set(n, 7).ok_or([]).len() * 10",
        7,
    ),
    (
        "find",
        "xs.find(|x| x % 2 == 1).ok_or(9) + xs.find(|x| x == 7).ok_or(9) * 10",
        91,
    ),
    (
        "find_index",
        "xs.find_index(|x| x == 3).ok_or(9) + xs.find_index(|x| x == 7).ok_or(9) * 10",
        93,
    ),
    (
        "try_map",
        "xs.try_map(|x| Ok(x + 1)).ok_or([]).fold(0, |s, x| s + x)",
        15,
    ),
    (
        "exchange",
        "xs.exchange(0, 4).ok_or([]).get_or(0, 9) + xs.exchange(0, n).ok_or([]).len() * 10",
        4,
    ),
    ("take", "xs.take(2).len() + xs.take(9).len() * 10", 52),
    ("drop", "xs.drop(1).get_or(0, 9) + xs.drop(9).len() * 10", 1),
    ("take_while", "xs.take_while(|x| x % 4 == x).len()", 4),
    (
        "drop_while",
        "xs.drop_while(|x| x % 4 == x).get_or(0, 9)",
        4,
    ),
    (
        "range",
        "List.range(n).fold(0, |s, x| s + x) + List.range(0).len()",
        10,
    ),
    (
        "repeat",
        "List.repeat(7, 3).fold(0, |s, x| s + x) + List.repeat(7, 0).len()",
        21,
    ),
];

#[test]
fn every_list_function_answers_what_ori_says() {
    for (name, answer, expected) in CASES {
        let package = Package::new(
            name,
            &format!(
                "small : Nat -> Nat
                 small(0) -> 0
                 small(Succ(_)) -> 1

                 main! : Host -> []
                 main!(host) -> (
                   n = 4 + small(host.args.len())
                   xs = [0, 1, 2, 3, n - 1]
                   host.exit!(U8.of_nat({answer}))
                 )"
            ),
        );
        assert_eq!(package.run(), *expected, "`{name}`: {answer}");
    }
}

/// A list's first elements are the same buffer holding fewer, so taking
/// them, splitting a list, and cutting one into blocks copy nothing: the
/// standard library's walk for `take` is answered as a view, and no walk of
/// it is left to run. What each answers is what the walk would have.
#[test]
fn taking_a_lists_first_elements_is_a_view_of_it() {
    let package = Package::new(
        "take-view",
        "main!(host) -> host.run_stdin!(app)

         app : {stdin: List(U8), *} -> Str
         app(input) -> answer(input.stdin.map(|b| b.to_nat() - 48))

         answer : List(Nat) -> Str
         answer(xs) -> (
           cut = xs.blocks(3)
           (front, back) = xs.split_at(2)
           [
             xs.take(4).fold(0, |s, x| s * 10 + x),
             xs.take(99).len(),
             front.len() * 10 + back.len(),
             cut.complete.map(|b| b.fold(0, |s, x| s * 10 + x)).fold(0, |s, x| s + x),
             cut.remainder.fold(0, |s, x| s * 10 + x),
           ].map(|n| n.to_str()).join(\",\")
         )",
    );
    for (input, said) in [
        ("12345678", "1234,8,26,579,78"),
        ("", "0,0,0,0,0"),
        ("123456", "1234,6,24,579,0"),
    ] {
        assert_eq!(
            support::run_file(&package.entry(), input.as_bytes()),
            (0, format!("{said}\n")),
            "{input}"
        );
    }
    let mut barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    faun_core::barb::optimize(&mut barb);
    let machine = faun_core::lower_to_machine_ir(&barb, &X86_64Linux.routines()).unwrap();
    assert!(!machine.render().contains("take_into"));
}
