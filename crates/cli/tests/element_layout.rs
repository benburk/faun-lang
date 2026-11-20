//! A list of small tags, or of tuples of small numbers, holds each element's
//! numbers packed by their bits in the list's own buffer: a block's
//! symbols, a literal byte or a match's length and distance, take four
//! bytes each, as the same numbers packed into a `U32` by hand do. Every
//! target reads back what was written, through matching, equality, joins,
//! replacing, reversing and sorting.
mod support;

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

use support::{Package, run_file};

/// Symbols gathered by appending and pushing, then read every way a
/// program reads a list: matched in a fold, compared, joined, replaced,
/// reversed, printed, and pairs of small numbers sorted.
const SYMBOLS: &str = r#"
    Symbol = [Literal(U8), Match(Nat, Nat)]

    gather : (Nat, Nat, List(Symbol)) -> List(Symbol)
    gather(0, _, symbols) -> symbols
    gather(Succ(left), x, symbols) if x % 3 == 0 ->
      gather(left, (x * 5 + 1) % 4096, symbols.append(Match(x % 256 + 3, x * 9 % 32768 + 1)))
    gather(Succ(left), x, symbols) -> gather(left, (x * 5 + 1) % 4096, symbols.append(Literal(U8.of_nat(x % 256))))

    weight : List(Symbol) -> Nat
    weight(symbols) -> symbols.fold(0, |total, symbol| symbol is (
      Literal(byte) then total + byte.to_nat()
      Match(length, distance) then total + length * 100000 + distance
    ))

    main!(host) -> (
      n = 200 + host.args.len()
      symbols = gather(n, 1, [])
      changed = [Literal(9)].concat(symbols).put(3, Match(258, 32768))
      pairs = List.range(n).map(|i| (i * 7 % 4, i * 37 % 300)).sort()
      same = symbols == gather(n, 1, []) & symbols.reverse().reverse() == symbols & symbols != changed
      printed = host.println!("${weight(symbols)} ${weight(changed)} ${weight(symbols.concat(changed))} ${same} ${symbols.take(3)} ${changed.drop(2).take(2)} ${pairs.take(4)} ${pairs.drop(n - 2)}")
      host.exit!(0)
    )
"#;

#[test]
fn a_list_of_small_tags_reads_back_what_was_written_on_every_target() {
    let package = Package::new("element-layout-symbols", SYMBOLS);
    let (status, expected) = run_file(&package.entry(), &[]);
    assert_eq!(status, 0);
    for target in ["x86_64-linux", "wasm32-wasi"] {
        let result = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(["run", "--target", target])
            .arg(package.entry())
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{target}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&result.stdout),
            expected,
            "{target}"
        );
    }
}

/// A million symbols gathered, then counted, the program waiting on its
/// input before it ends, so its peak memory can be read while it lives.
fn gathering(symbol: &str, appended: (&str, &str), weighed: &str) -> String {
    format!(
        r#"
    gather : (Nat, Nat, List({symbol})) -> List({symbol})
    gather(0, _, symbols) -> symbols
    gather(Succ(left), x, symbols) if x % 3 == 0 -> gather(left, (x * 5 + 1) % 65536, symbols.append({}))
    gather(Succ(left), x, symbols) -> gather(left, (x * 5 + 1) % 65536, symbols.append({}))

    main!(host) -> (
      symbols = gather(1000000, 1, [])
      printed = host.println!("${{symbols.fold(0, |total, symbol| {weighed})}}")
      waited = host.stdin.read!(1)
      host.exit!(0)
    )
"#,
        appended.0, appended.1
    )
}

/// The most memory the program at `entry`, built for x86-64, held, in
/// kilobytes, and what it printed.
fn peak(entry: &std::path::Path) -> (u64, String) {
    let image = entry.with_file_name("image");
    let built = Command::new(env!("CARGO_BIN_EXE_faun"))
        .args(["build", "-o"])
        .arg(&image)
        .arg(entry)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let mut child = Command::new(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    let status = std::fs::read_to_string(format!("/proc/{}/status", child.id())).unwrap();
    let held = status
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|rest| rest.trim().trim_end_matches("kB").trim().parse().ok())
        .expect("a peak resident size");
    child.stdin.take().unwrap().write_all(b"x").unwrap();
    assert!(child.wait().unwrap().success());
    (held, line.trim().to_owned())
}

#[test]
fn a_list_of_small_tags_holds_as_little_as_the_numbers_packed_by_hand() {
    let natural = Package::new(
        "element-layout-tags",
        &format!(
            "Symbol = [Literal(U8), Match(Nat, Nat)]

    weigh : (Nat, Symbol) -> Nat
    weigh(total, Literal(byte)) -> total + byte.to_nat()
    weigh(total, Match(length, distance)) -> total + length + distance
{}",
            gathering(
                "Symbol",
                ("Match(x % 256 + 3, x % 32768 + 1)", "Literal(U8.of_nat(x))"),
                "weigh(total, symbol)",
            )
        ),
    );
    let packed = Package::new(
        "element-layout-words",
        &gathering(
            "U32",
            (
                "U32.of_nat((x % 256 + 3) * 65536 + x % 32768 + 1)",
                "U32.of_nat(x % 256)",
            ),
            "if symbol < 65536 then total + symbol.to_nat() else total + symbol.shift_right(16).to_nat() + (symbol & 0xffff).to_nat()",
        ),
    );
    let (tags, said) = peak(&natural.entry());
    let (words, answer) = peak(&packed.entry());
    assert_eq!(said, answer);
    // Six bytes a symbol, each number in bytes of its own, would hold half
    // as much again.
    assert!(
        tags * 10 < words * 11,
        "the symbols held {tags} kB, the words {words} kB"
    );
}
