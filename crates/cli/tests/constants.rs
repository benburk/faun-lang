//! A constant is worked out once, however often it is named: one that does
//! work and is named in a walk is worked out by the entry and handed down,
//! one that folds is a known value, and one read once is left where it is
//! read, to be fused with what reads it.
mod support;

use faun_x86_64_linux::X86_64Linux;
use support::{Package, run_counted};

/// CRC-32 a byte at a time, through a table named inside the walk: too
/// large to fold, so worked out as the program runs.
const CRC: &str = r"
    table : List(U32)
    table = List.range(256).map(|n| entry(U32.of_nat(n), 8))

    entry : (U32, Nat) -> U32
    entry(register, 0) -> register
    entry(register, Succ(bits)) if (register & 1) == 1 ->
      entry(0xedb88320 ^ register.shift_right(1), bits)
    entry(register, Succ(bits)) -> entry(register.shift_right(1), bits)

    crc : (U32, List(U8)) -> U32
    crc(register, []) -> register
    crc(register, [byte, *rest]) ->
      crc(table.get((register ^ U32.of_u8(byte)).to_nat() & 0xff).ok_or(0) ^ register.shift_right(8), rest)

    app : {stdin: List(U8), *} -> Str
    app(input) -> (!crc(0xffffffff, input.stdin)).to_nat().to_str()

    main!(host) -> host.run_stdin!(app)
";

fn crc32(bytes: &[u8]) -> u32 {
    let mut register = !0u32;
    for &byte in bytes {
        register ^= u32::from(byte);
        for _ in 0..8 {
            register = if register & 1 == 1 {
                0xedb8_8320 ^ (register >> 1)
            } else {
                register >> 1
            };
        }
    }
    !register
}

fn optimized(package: &Package) -> barb::Program {
    let mut program =
        faun_frontend::lower_to_barb(&package.entry(), &faun_driver::platform(&X86_64Linux))
            .unwrap();
    barb::optimize(&mut program);
    barb::validate(&program).unwrap();
    program
}

/// Whether any definition is named `name`, or takes a parameter named so.
fn named(program: &barb::Program, name: &str) -> (bool, bool) {
    let defined = program
        .function_ids()
        .any(|id| program.name(program.function(id).name) == name);
    let taken = program.function_ids().any(|id| {
        program
            .parameter_names(id)
            .any(|parameter| parameter == name)
    });
    (defined, taken)
}

#[test]
fn a_table_named_in_a_walk_is_built_once() {
    let package = Package::new("constant-crc", CRC);
    let bytes: Vec<u8> = (0..128u32)
        .map(|n| u8::try_from(n * 37 % 251).unwrap())
        .collect();
    let mut spent = Vec::new();
    for len in [64, 128] {
        let (status, written, fuel) = run_counted(&package.entry(), &bytes[..len]);
        assert_eq!(status, 0);
        assert_eq!(written.trim(), crc32(&bytes[..len]).to_string());
        spent.push(fuel);
    }
    // Building the table costs far more than a byte. Built once, 64 more
    // bytes cost a fraction of what the first 64 and the table did; built
    // once a byte, they would cost about as much again.
    let (first, both) = (spent[0], spent[1]);
    assert!(
        (both - first) * 4 < first,
        "64 bytes and the table took {first}, 64 more {}",
        both - first
    );
    let (_, taken) = named(&optimized(&package), "table");
    assert!(taken, "the table is handed to the walk");
}

#[test]
fn a_constant_read_once_is_left_where_it_is_read() {
    let package = Package::new(
        "constant-once",
        r"
        total : Nat
        total = List.range(100000).map(|n| n * 3).sum()

        main!(host) -> host.exit!(U8.of_nat(total % 256))
    ",
    );
    assert_eq!(
        package.run(),
        u32::try_from(3 * 4_999_950_000u64 % 256).unwrap()
    );
    assert_eq!(named(&optimized(&package), "total"), (false, false));
}

#[test]
fn a_constant_that_folds_is_a_known_value() {
    let package = Package::new(
        "constant-folds",
        r"
        squares : List(Nat)
        squares = List.range(8).map(|n| n * n)

        sum : (List(U8), Nat) -> Nat
        sum([], total) -> total
        sum([byte, *rest], total) -> sum(rest, total + squares.get(byte.to_nat() % 8).ok_or(0))

        app : {stdin: List(U8), *} -> Str
        app(input) -> sum(input.stdin, 0).to_str()

        main!(host) -> host.run_stdin!(app)
    ",
    );
    let (status, written, _) = run_counted(&package.entry(), b"faun");
    let expected: u32 = b"faun".iter().map(|&byte| u32::from(byte % 8).pow(2)).sum();
    assert_eq!((status, written.trim()), (0, expected.to_string().as_str()));
    assert_eq!(named(&optimized(&package), "squares"), (false, false));
}
