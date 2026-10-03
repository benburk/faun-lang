//! How long the frontend takes to load, resolve and type-check a program,
//! the standard library with it: an empty library, which is the standard
//! library's own cost, then programs each built to stress one thing the
//! checker does, at a size where a cost that grows faster than the program
//! shows.
//!
//! `cargo bench -p faun --bench check`, or with a name to run the cases
//! whose names hold it.

use std::fmt::Write as _;
use std::hint::black_box;
use std::path::Path;
use std::time::{Duration, Instant};

use faun::blessed::PreludeIds;
use faun::{check, declarations, modules, resolve};

const RUNS: usize = 5;

fn main() {
    let only = std::env::args()
        .skip(1)
        .find(|argument| !argument.starts_with('-'));
    let directory = std::env::temp_dir().join(format!("faun-check-bench-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a temporary directory");
    println!(
        "{:26} {:>9} {:>9} {:>9} {:>9}",
        "case", "load", "resolve", "check", "total"
    );
    for (name, source) in cases() {
        if only
            .as_ref()
            .is_some_and(|only| !name.contains(only.as_str()))
        {
            continue;
        }
        let entry = directory.join(format!("{}.fn", name.replace(' ', "-")));
        std::fs::write(&entry, &source).expect("the case is written");
        benchmark(&name, &entry);
    }
    let _ = std::fs::remove_dir_all(&directory);
}

/// A program of a given size.
type Build = fn(usize) -> String;

/// Each case by name, and its source. A pathological case is built at two
/// sizes, the second twice the first, so how its cost grows shows: twice
/// the time is linear, four times quadratic.
fn cases() -> Vec<(String, String)> {
    let mut cases = vec![("standard library".to_owned(), String::new())];
    let scaled: [(&str, Build, usize); 11] = [
        ("signed definitions", signed_definitions, 2_000),
        ("unsigned definitions", unsigned_definitions, 1_000),
        ("recursive group", recursive_group, 300),
        ("nested calls", nested_calls, 200),
        ("binding chain", binding_chain, 1_000),
        ("doubling types", doubling_types, 12),
        ("wide record", wide_record, 100),
        ("wide tags", wide_tags, 300),
        ("method chain", method_chain, 500),
        ("list literal", list_literal, 2_500),
        ("print statements", print_statements, 5_000),
    ];
    for (name, build, size) in scaled {
        // A type that doubles at each step doubles again with one more.
        let larger = if name == "doubling types" {
            size + 2
        } else {
            size * 2
        };
        for size in [size, larger] {
            cases.push((format!("{name} {size}"), build(size)));
        }
    }
    cases
}

/// Definitions each calling the one before, each with a signature.
fn signed_definitions(count: usize) -> String {
    let mut source = String::from("f0 : Nat -> Nat\nf0(n) -> n\n");
    for i in 1..count {
        let before = i - 1;
        writeln!(source, "f{i} : Nat -> Nat\nf{i}(n) -> f{before}(n) + 1").unwrap();
    }
    source
}

/// The same with no signatures, so each is inferred and generalized.
fn unsigned_definitions(count: usize) -> String {
    let mut source = String::from("f0(n) -> n\n");
    for i in 1..count {
        let before = i - 1;
        writeln!(source, "f{i}(n) -> f{before}(n) + 1").unwrap();
    }
    source
}

/// Definitions calling each other round a ring, with no signatures, so
/// they are inferred as one component.
fn recursive_group(count: usize) -> String {
    let mut source = String::new();
    for i in 0..count {
        let next = (i + 1) % count;
        writeln!(source, "g{i}(Succ(n)) -> g{next}(n)\ng{i}(Zero) -> 0").unwrap();
    }
    source
}

/// One call nested `depth` deep.
fn nested_calls(depth: usize) -> String {
    let mut source =
        String::from("inc : Nat -> Nat\ninc(n) -> n + 1\n\ndeep : Nat -> Nat\ndeep(n) -> ");
    source.push_str(&"inc(".repeat(depth));
    source.push('n');
    source.push_str(&")".repeat(depth));
    source.push('\n');
    source
}

/// One body binding `count` names, each from the one before.
fn binding_chain(count: usize) -> String {
    let mut source = String::from("chain : Nat -> Nat\nchain(x0) ->\n");
    for i in 1..count {
        let before = i - 1;
        writeln!(source, "  x{i} = x{before} + 1").unwrap();
    }
    writeln!(source, "  x{}", count - 1).unwrap();
    source
}

/// Each definition pairs the one before, so its type is twice as large:
/// the last is a tree of `2^depth` naturals. A checker that shares a type
/// rather than copying it pays for `depth`, not `2^depth`.
fn doubling_types(depth: usize) -> String {
    let mut source = String::from("pair(a) -> (a, a)\n\np0 = 0\n");
    for i in 1..=depth {
        let before = i - 1;
        writeln!(source, "p{i}() -> pair(p{before}())").unwrap();
    }
    source
}

/// A record of `count` fields, each field then read.
fn wide_record(count: usize) -> String {
    let fields: Vec<String> = (0..count).map(|i| format!("f{i}: {i}")).collect();
    let reads: Vec<String> = (0..count).map(|i| format!("r.f{i}")).collect();
    format!(
        "record = {{{}}}\n\nsum : Nat\nsum =\n  r = record\n  {}\n",
        fields.join(", "),
        reads.join(" + ")
    )
}

/// A closed row of `count` tags, a clause for each.
fn wide_tags(count: usize) -> String {
    let tags: Vec<String> = (0..count).map(|i| format!("T{i}")).collect();
    let mut source = format!("number : [{}] -> Nat\n", tags.join(", "));
    for (i, tag) in tags.iter().enumerate() {
        writeln!(source, "number({tag}) -> {i}").unwrap();
    }
    source
}

/// One method called `count` times in a row.
fn method_chain(count: usize) -> String {
    format!(
        "chain : Nat -> Nat\nchain(n) -> n{}\n",
        ".add(1)".repeat(count)
    )
}

/// A list literal of `count` numerals, each given its type.
fn list_literal(count: usize) -> String {
    let items: Vec<String> = (0..count).map(|i| i.to_string()).collect();
    format!("numbers : List(U32)\nnumbers = [{}]\n", items.join(", "))
}

/// An application writing one line `count` times, each its own statement.
fn print_statements(count: usize) -> String {
    let mut source = String::from("import std.host {Host}\n\nmain! : Host -> []\nmain!(host) ->\n");
    for _ in 0..count {
        source.push_str("  host.println!(\"hello\")\n");
    }
    source.push_str("  host.exit!(0)\n");
    source
}

/// Time each phase at its best of several runs, and print them.
fn benchmark(name: &str, entry: &Path) {
    let host = faun::standard_path().with_file_name("hosts/x86_64-linux.fn");
    let load = || modules::load_program(entry, faun::standard_path(), &host);
    if let Err(diagnostic) = load()
        .map_err(|error| error.to_string())
        .and_then(|loaded| {
            let prelude = PreludeIds::find_in(&loaded).map_err(|error| error.message)?;
            let resolved = resolve::resolve_names(loaded).map_err(|error| error.to_string())?;
            check::type_check(declarations::normalize(resolved), prelude)
                .map(drop)
                .map_err(|error| error.to_string())
        })
    {
        panic!("{name} is not a well-typed program:\n{diagnostic}");
    }
    let (mut loading, mut resolving, mut checking) = (Duration::MAX, Duration::MAX, Duration::MAX);
    for _ in 0..RUNS {
        let started = Instant::now();
        let loaded = load().expect("loaded before");
        let loaded_at = Instant::now();
        let prelude = PreludeIds::find_in(&loaded).expect("found before");
        let resolved = resolve::resolve_names(loaded).expect("resolved before");
        let resolved_at = Instant::now();
        let checked = check::type_check(declarations::normalize(resolved), prelude);
        let checked_at = Instant::now();
        black_box(checked.expect("checked before"));
        loading = loading.min(loaded_at - started);
        resolving = resolving.min(resolved_at - loaded_at);
        checking = checking.min(checked_at - resolved_at);
    }
    let total = loading + resolving + checking;
    println!(
        "{name:26} {:>9} {:>9} {:>9} {:>9}",
        shown(loading),
        shown(resolving),
        shown(checking),
        shown(total)
    );
}

fn shown(duration: Duration) -> String {
    format!("{:.2}ms", duration.as_secs_f64() * 1000.0)
}
