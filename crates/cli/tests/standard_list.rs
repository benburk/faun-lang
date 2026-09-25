//! The standard list answers what Ori's does. Each case is a Faun program
//! lowered for x86-64 and run on the reference interpreter, so what it
//! checks is the library and the tiers above a target, whatever any one
//! backend can yet hold: lists of lists, and counts with no bound.

use std::fs;
use std::path::PathBuf;

use faun_core::ir::FunctionId;
use faun_core::ir::evaluate::{self, Error, Host, HostResult, Memory};
use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;
use num_bigint::BigUint;

/// Each case: what it exercises, the status it exits with, and what it
/// leaves with from `xs`, `[0 1 2 3 4]`, and `n`, its length.
const CASES: &[(&str, &str, u32)] = &[
    ("len", "xs.len() + xs.take(0).len()", 5),
    (
        "is_empty",
        "xs.is_empty().to_nat() + xs.take(0).is_empty().to_nat() * 2",
        2,
    ),
    ("append", "xs.append(9).get_or(5 0)", 9),
    (
        "extend",
        "xs.extend([7 8]).get_or(6 0) + xs.extend([7 8]).len() * 10",
        78,
    ),
    (
        "prepend",
        "xs.prepend(9).get_or(0 0) + xs.prepend(9).len() * 10",
        69,
    ),
    ("map", "xs.map(|x| x * 2).get_or(4 0)", 8),
    (
        "map2",
        "xs.map2([10 20] |a b| a + b).fold(0 |s x| s + x)",
        31,
    ),
    ("flat_map", "xs.flat_map(|x| [x x]).len()", 10),
    ("flatten", "[[1 2] [] [3]].flatten().len()", 3),
    (
        "join",
        "[[1] [2 3] [4]].join([0 0]).len() + [[7]].join([0]).len() * 10",
        18,
    ),
    ("filter", "xs.filter(|x| x % 2 == 1).fold(0 |s x| s + x)", 4),
    ("count", "xs.count(|x| x % 2 == 0)", 3),
    (
        "any",
        "xs.any(|x| x == 2).to_nat() + xs.any(|x| x == 9).to_nat() * 2",
        1,
    ),
    (
        "all",
        "[1 3].all(|x| x % 2 == 1).to_nat() + xs.all(|x| x % 2 == 1).to_nat() * 2",
        1,
    ),
    ("fold", "xs.fold(0 |s x| s * 10 + x)", 1_234 % 256),
    (
        "fold_right",
        "xs.fold_right(0 |x s| s * 10 + x)",
        43_210 % 256,
    ),
    (
        "trail",
        "xs.trail(0 |s x| s + x).get_or(4 0) + xs.trail(0 |s x| s + x).len() * 20",
        110,
    ),
    (
        "reverse",
        "xs.reverse().get_or(0 9) + xs.reverse().len() * 10",
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
    ("get_or", "xs.get_or(2 9) + xs.get_or(n 9) * 10", 92),
    (
        "set",
        "xs.set(1 7).ok_or([]).get_or(1 0) + xs.set(n 7).ok_or([]).len() * 10",
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
    ("take", "xs.take(2).len() + xs.take(9).len() * 10", 52),
    ("drop", "xs.drop(1).get_or(0 9) + xs.drop(9).len() * 10", 1),
    ("take_while", "xs.take_while(|x| x % 4 == x).len()", 4),
    ("drop_while", "xs.drop_while(|x| x % 4 == x).get_or(0 9)", 4),
    (
        "range",
        "List.range(n).fold(0 |s x| s + x) + List.range(0).len()",
        10,
    ),
    (
        "repeat",
        "List.repeat(7 3).fold(0 |s x| s + x) + List.repeat(7 0).len()",
        21,
    ),
];

#[test]
fn every_list_function_answers_what_ori_says() {
    let root = std::env::temp_dir().join(format!("faun-standard-list-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    for (name, answer, expected) in CASES {
        let status = run(&root, name, answer);
        assert_eq!(status, *expected, "`{name}`: {answer}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// What a program exits with, where `xs` is built from what it is handed
/// so that nothing is folded away before it runs. An exit status is a
/// byte, so the answer is taken as one.
fn run(root: &std::path::Path, name: &str, answer: &str) -> u32 {
    let source: PathBuf = root.join(format!("{name}.fn"));
    fs::write(
        &source,
        format!(
            "import std.host {{Host}}\n\n\
             small : Nat -> Nat\nsmall(0) -> 0\nsmall(Succ(_)) -> 1\n\n\
             main! : Host -> []\nmain!(host) ->\n  \
             n = 4 + small(host.argc)\n  xs = [0 1 2 3 n - 1]\n  host.exit!(({answer}) % 256)\n"
        ),
    )
    .unwrap();
    let mut barb = faun::lower_to_barb(&source, &X86_64Linux)
        .unwrap_or_else(|error| panic!("`{name}`: {}", error.message));
    faun_core::barb::optimize(&mut barb);
    let machine = faun_core::lower_to_machine_ir(&mut barb, &X86_64Linux.routines())
        .unwrap_or_else(|error| panic!("`{name}`: {error}"));
    let prepared = X86_64Linux
        .prepare(&machine)
        .unwrap_or_else(|error| panic!("`{name}`: {error}"));
    let main = prepared
        .functions()
        .iter()
        .position(|function| prepared.name(function.name) == "main!")
        .map(FunctionId::at)
        .expect("an entry");
    let evaluation = evaluate::evaluate(
        &prepared,
        main,
        &[BigUint::from(1u8)],
        evaluate::Config {
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut Exit,
    )
    .unwrap_or_else(|error| panic!("`{name}`: {error:?}"));
    let halted = evaluation.halted().expect("a program that exits");
    u32::try_from(&halted[0]).expect("a status")
}

/// A host that only knows how to leave.
struct Exit;

impl Host for Exit {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        if name == "exit!" {
            Ok(HostResult::Halt(args.to_vec()))
        } else {
            Err(Error::Host(name.to_owned()))
        }
    }
}
