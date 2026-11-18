//! A buffer nothing else holds is written where it lies, even where the
//! program reads it around the write: a run of a list joined to it, and a
//! read of a list written beside it in the same record, each leave the list
//! held once when it is written, so a step costs what it writes and not the
//! whole list.
mod support;

use support::{Package, run_counted};

/// The fuel a program spends on `steps` bytes of input, which it takes as
/// how many steps to make, and what it prints.
fn spent(package: &Package, steps: usize) -> (String, u64) {
    let (status, written, fuel) = run_counted(&package.entry(), &vec![0; steps]);
    assert_eq!(status, 0);
    (written.trim().to_owned(), fuel)
}

/// Whether 100 steps more cost far less, a step, than the `len` elements of
/// the list a copy would move.
fn per_step(package: &Package, len: u64) -> (String, String, u64) {
    let (few, first) = spent(package, 100);
    let (many, second) = spent(package, 200);
    let step = (second - first) / 100;
    assert!(
        step * 4 < len,
        "a step cost {step} fuel, as if the {len} elements were copied"
    );
    (few, many, step)
}

#[test]
fn a_list_joined_to_a_run_of_itself_grows_where_it_lies() {
    // LZ77's copy: three bytes from a distance back, joined to the window.
    let package = Package::new(
        "in-place-run",
        r#"
        grow : (List(U8), Nat, Nat) -> List(U8)
        grow(out, _, 0) -> out
        grow(out, back, Succ(left)) ->
          grow(out.concat(out.drop(out.len() - back).take(3)), back % 7 + 3, left)

        app : {stdin: List(U8), *} -> Str
        app(input) -> (
          out = grow(List.range(2000).map(|n| U8.of_nat(n % 251)), 3, input.stdin.len())
          "${out.len()} ${out.fold(0, |sum, byte| sum + byte.to_nat())} ${out.drop(out.len() - 6)}"
        )

        main!(host) -> host.run_stdin!(app)
    "#,
    );
    let expected = |steps: usize| {
        let mut out: Vec<u8> = (0..2000u32)
            .map(|n| u8::try_from(n % 251).unwrap())
            .collect();
        let mut back = 3;
        for _ in 0..steps {
            let from = out.len() - back;
            out.extend_from_within(from..from + 3);
            back = back % 7 + 3;
        }
        let sum: u64 = out.iter().map(|&byte| u64::from(byte)).sum();
        let last: Vec<String> = out[out.len() - 6..].iter().map(u8::to_string).collect();
        format!("{} {sum} [{}]", out.len(), last.join(", "))
    };
    let (few, many, _) = per_step(&package, 2000);
    assert_eq!(few, expected(100));
    assert_eq!(many, expected(200));
}

#[test]
fn a_run_of_words_joined_to_its_list_keeps_every_claim() {
    // Elements holding counts: each copied word is claimed again, and the
    // runs taken from inside, before and across the list are each what
    // they were before the join.
    let package = Package::new(
        "in-place-words",
        r#"
        grow : (List(Str), Nat) -> List(Str)
        grow(out, 0) -> out
        grow(out, Succ(left)) -> grow(out.concat(out.drop(left % out.len()).take(2)), left)

        app : {stdin: List(U8), *} -> Str
        app(input) -> (
          words = ["a", "bb", "ccc"].map(|word| word.concat("!"))
          doubled = words.concat(words)
          front = words.drop(1).concat(words.take(2))
          grown = grow(words, input.stdin.len())
          "${doubled.join(",")} ${front.join(",")} ${grown.join(",")}"
        )

        main!(host) -> host.run_stdin!(app)
    "#,
    );
    let (written, _) = spent(&package, 3);
    assert_eq!(
        written,
        "a!,bb!,ccc!,a!,bb!,ccc! bb!,ccc!,a!,bb! a!,bb!,ccc!,ccc!,bb!,ccc!,a!,bb!"
    );
}

#[test]
fn a_read_beside_a_write_of_the_same_list_is_made_before_it() {
    // Hash chains' insert: the second field reads the head the first
    // writes over, so the read is worked out first.
    let package = Package::new(
        "in-place-record",
        r#"
        Chains = {head: List(Nat), prev: List(Nat)}

        insert : (Chains, Nat) -> Chains
        insert({head, prev}, at) ->
          {head: head.put(at * 7 % 1024, at + 1), prev: prev.put(at, head.get(at * 7 % 1024).ok_or(0))}

        walk : (Chains, Nat, Nat) -> Chains
        walk(chains, at, end) if at >= end -> chains
        walk(chains, at, end) -> walk(insert(chains, at), at + 1, end)

        app : {stdin: List(U8), *} -> Str
        app(input) -> (
          {head, prev} = walk({head: List.repeat(0, 1024), prev: List.repeat(0, 256)}, 0, input.stdin.len())
          "${head.sum()} ${prev.sum()}"
        )

        main!(host) -> host.run_stdin!(app)
    "#,
    );
    let expected = |steps: usize| {
        let mut head = vec![0usize; 1024];
        let mut prev = vec![0usize; 256];
        for (at, slot) in prev.iter_mut().enumerate().take(steps) {
            let key = at * 7 % 1024;
            *slot = head[key];
            head[key] = at + 1;
        }
        format!(
            "{} {}",
            head.iter().sum::<usize>(),
            prev.iter().sum::<usize>()
        )
    };
    let (few, many, _) = per_step(&package, 1024);
    assert_eq!(few, expected(100));
    assert_eq!(many, expected(200));
}
