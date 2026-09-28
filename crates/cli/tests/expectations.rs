//! `expect`: what a package claims of its definitions, which `faun test`
//! asks, and which checking a package checks whether or not it is asked.

mod support;

use std::fs;

use support::Package;

/// Every expectation in the package is asked, the entry's and those of the
/// modules it imports, numbered in the order the modules were loaded; the
/// test entry takes the place of the application's own `main!`.
#[test]
fn a_test_build_asks_every_expectation_in_the_package() {
    let package = Package::new(
        "expectations",
        "import halves {half}

         double : Nat -> Nat
         double(n) -> n * 2

         expect double(2) == 4
         expect double(half(6)) == 7
         expect
           doubled = [1, 2, 3].map(double)
           doubled.len() == 3
             & doubled.last().ok_or(0) == 6

         main!(host) -> host.exit!(9)",
    );
    fs::write(
        package.entry().with_file_name("halves.fn"),
        "export {half}\n\nhalf : Nat -> Nat\nhalf(n) -> n / 2\n\nexpect half(7) == 3\nexpect half(1) == 1\n",
    )
    .unwrap();

    let (failed, count) = support::test_file(&package.entry());
    assert_eq!(count, 5);
    assert_eq!(failed, ["main.fn:9", "halves.fn:7"]);
    // Built as an application, the package is its own `main!`.
    assert_eq!(package.run(), 9);
}

/// A record literal handed alone to a function pairing two values of one
/// shape is that function applied a field at a time, each step answering a
/// record, as Ori's record builders are: the signature asks, not the name.
#[test]
fn a_record_literal_builds_through_a_pairing() {
    let package = Package::new(
        "record-builder",
        "both : (Result(a, e), Result(b, e), (a, b) -> c) -> Result(c, e)
         both(Ok(x), Ok(y), f) -> Ok(f(x, y))
         both(Err(e), _, _) -> Err(e)
         both(_, Err(e), _) -> Err(e)

         dims : (Str, Str, Str) -> Result({width: Nat, height: Nat, depth: Nat}, [Malformed])
         dims(w, h, d) -> both({width: Nat.from_str(w), height: Nat.from_str(h), depth: Nat.from_str(d)})

         expect dims(\"3\", \"4\", \"5\") == Ok({width: 3, height: 4, depth: 5})
         expect dims(\"3\", \"x\", \"5\") == Err(Malformed)",
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 2));
}

/// Generated expressions must not need spare bytes in their source span.
#[test]
fn record_builders_do_not_depend_on_whitespace() {
    for (name, padding) in [("compact", String::new()), ("padded", " ".repeat(300))] {
        let package = Package::new(
            &format!("record-builder-{name}"),
            &format!(
                "both : (Result(a, e), Result(b, e), (a, b) -> c) -> Result(c, e)
                 both(Ok(x), Ok(y), f) -> Ok(f(x, y))
                 both(Err(e), _, _) -> Err(e)
                 both(_, Err(e), _) -> Err(e)

                 built : Result({{a: Nat, b: Bool, c: Nat, d: Nat, e: Nat, f: Nat, g: Nat, h: Nat, i: Nat, j: Nat}}, [Malformed])
                 built() -> both({{a: Ok(1), b: Ok(True), c: Ok(3), d: Ok(4), e: Ok(5), f: Ok(6), g: Ok(7), h: Ok(8), i: Ok(9), j: Ok(10){padding}}})
                 expect built() == Ok({{a: 1, b: True, c: 3, d: 4, e: 5, f: 6, g: 7, h: 8, i: 9, j: 10}})"
            ),
        );
        assert_eq!(support::test_file(&package.entry()), (Vec::new(), 1));
    }
}

/// A method a type's block writes without a signature is called with a dot
/// like any other, in its module and from another.
#[test]
fn a_method_without_a_signature_is_called_with_a_dot() {
    let package = Package::new(
        "unsigned-method",
        "import boxes {Box}

         expect Box.of(4).twice() == 8",
    );
    fs::write(
        package.entry().with_file_name("boxes.fn"),
        "export {Box}\n\nBox : Nat.(\n  of : Nat -> Box\n  of(n) -> Box(n)\n\n  twice(Box(n)) -> n * 2\n)\n\nexpect Box.of(3).twice() == 6\n",
    )
    .unwrap();
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 2));
}

/// A closed record and a tuple say themselves as Ori writes them: a
/// record's fields in the order of their names, whatever order they were
/// written in, and a tuple's members in order, each by its own `to_str`.
#[test]
fn records_and_tuples_say_themselves() {
    let package = Package::new(
        "structural-to-str",
        "expect {y: 2, x: 1}.to_str() == \"{x: 1, y: 2}\"
         expect (1, \"a\").to_str() == \"(1, a)\" & {}.to_str() == \"{}\"
         expect {name: \"n\", inner: {z: [1, 2], a: (True, -3)}}.to_str() == \"{inner: {a: (True, -3), z: [1, 2]}, name: n}\"",
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 3));
}

/// A constructor its module exports with its type's `.*` may be imported
/// by itself, as Ori imports `Read` from the host. One exported only with
/// its type, without `.*`, may not: see `refused/`.
#[test]
fn a_constructor_is_imported_by_itself() {
    let package = Package::new(
        "constructor-import",
        "import shapes {Circle, area}

         expect area(Circle(3)) == 27",
    );
    fs::write(
        package.entry().with_file_name("shapes.fn"),
        "export {Shape.*, Hidden, area}\n\nShape : [Circle(Nat), Square(Nat)]\nHidden : [Secret]\n\narea : Shape -> Nat\narea(Circle(r)) -> 3 * r * r\narea(Square(s)) -> s * s\n",
    )
    .unwrap();
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 1));
}

#[test]
fn a_package_without_expectations_has_nothing_to_ask() {
    let package = Package::new("no-expectations", "main!(host) -> host.exit!(0)");
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 0));
}

/// `faun test` tells an expectation that does not hold as it tells any
/// diagnostic, at the line it was written, and fails with how many did.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn a_failing_expectation_is_told_as_a_diagnostic() {
    let package = Package::new(
        "failing-expectation",
        "expect 1 + 1 == 2

         expect 1 + 1 == 3",
    );
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_faun"))
        .arg("test")
        .arg(package.entry())
        .output()
        .unwrap();
    let told = String::from_utf8(output.stderr).unwrap();
    assert!(!output.status.success(), "{told}");
    // The package's source starts after the host import and a blank line.
    let expected = format!(
        "error: this expectation does not hold\n \
         --> {}:5:1\n  \
         |\n\
         5 | expect 1 + 1 == 3\n  \
         | ^^^^^^^^^^^^^^^^^\n\
         \n\
         error: 1 of 2 expectations does not hold\n",
        package.entry().display()
    );
    assert_eq!(told, expected);
}

/// The standard library is a package like any other, and holds what it
/// expects of itself.
#[test]
fn the_standard_library_holds_its_expectations() {
    let (failed, count) = support::test_file(faun::standard_path());
    assert!(count > 0);
    assert_eq!(failed, Vec::<String>::new());
}

/// Wide words work bit by bit. The standard library holds what every
/// target runs, and neither the 6502 nor wasm32 yet holds a 64-bit word
/// worked out at run time, so these are asked here.
#[test]
fn wide_words_work_bit_by_bit() {
    let package = Package::new(
        "wide-words",
        "expect U64.of_nat(1).shift_left(63).rotate_left(1) == 1
         expect U64.of_nat(1).rotate_right(1) == 0x8000000000000000
         expect (U64.of_nat(0xff00ff00ff00ff00) & 0x0ff00ff00ff00ff0) == 0x0f000f000f000f00
         expect (U32.of_nat(0xf0f0f0f0) ^ 0xffffffff) == 0x0f0f0f0f
         expect U16.of_nat(0x8001).rotate_left(4) == 0x0018",
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 5));
}

/// A package asks its own expectations, which may call into a package it
/// depends on, and not that package's, which its own test run asks.
#[test]
fn a_dependency_is_called_and_its_expectations_are_its_own() {
    let package = Package::new(
        "with-dependency",
        "package {shapes: \"vendor/shapes\"}

         import shapes {double_square}

         expect double_square(3) == 18
         expect double_square(1) == 3",
    );
    let vendor = package.entry().with_file_name("vendor");
    fs::create_dir_all(&vendor).unwrap();
    fs::write(
        vendor.join("shapes.fn"),
        "package {}\n\nexport {double_square}\n\ndouble_square : Nat -> Nat\ndouble_square(n) -> n * n * 2\n\nexpect double_square(0) == 1\n",
    )
    .unwrap();
    let (failed, count) = support::test_file(&package.entry());
    assert_eq!((failed, count), (vec!["main.fn:8".to_owned()], 2));
}

/// Decimal numerals are floats, `F64` where nothing else decides, and the
/// basic operations round as the standard says, on the reference
/// interpreter.
#[test]
fn floats_read_add_divide_and_say_themselves() {
    let package = Package::new(
        "floats",
        "third : F32
         third() -> F32.div(1.0, 3.0)

         expect 0.1.add(0.2).to_str() == \"0.30000000000000004\"
         expect F32.add(0.1, 0.2) == 0.3
         expect third().to_str() == \"0.33333334\"
         expect (-2.5).to_str() == \"-2.5\" & 2.5E2 == 250.0 & 1.0e-12.to_str() == \"1.0e-12\"
         expect F64.from_str(\"0.1\") == Ok(0.1) & F32.from_str(\"1e\") == Err(Malformed)
         expect F32.sqrt(2.0).to_bits() == 0x3fb504f3 & F32.nan() == F32.nan()",
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 6));
}

/// Bitwise operations and powers of numbers read from what a program is
/// handed, which nothing works out before it runs: each is recognized and
/// answered as one operation, at a word where its operands' ranges say
/// one holds it and on the natural runtime past that.
#[test]
fn bitwise_and_powers_of_numbers_read_at_run_time() {
    let package = Package::new(
        "bitwise-input",
        "main!(host) -> host.run_stdin!(app)

         app : {stdin: List(U8), *} -> Str
         app(input) ->
           text = Str.from_utf8(input.stdin).ok_or(\"\")
           answer(text.trim().split(\" \").map(number))

         number : Str -> Nat
         number(word) -> Nat.from_str(word).ok_or(0)

         answer : List(Nat) -> Str
         answer([a, b, *_]) -> Str.join([
           a.and(b), a.or(b), a.xor(b), a.pow(b % 3), (b % 3).pow(a % 5),
           U32.of_nat(a).rotate_left(b).to_nat(), U32.of_nat(a).shift_right(b % 40).to_nat(),
           U8.of_nat(a).and(U8.of_nat(b)).to_nat(),
         ].map(|n| n.to_str()), \" \")
         answer(_) -> \"\"",
    );
    let cases = [
        ("12 10", "8 14 6 12 1 12288 0 8"),
        ("0 0", "0 0 0 1 1 0 0 0"),
        (
            "340282366920938463463374607431768211457 18446744073709551617",
            "1 340282366920938463481821351505477763073 \
             340282366920938463481821351505477763072 \
             115792089237316195423570985008687907853950549399482440966384333222776666062849 \
             4 2 0 1",
        ),
        (
            "4294967295 65",
            "65 4294967295 4294967230 18446744065119617025 1 4294967295 127 65",
        ),
    ];
    for (input, said) in cases {
        let said: String = said.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(
            support::run_file(&package.entry(), input.as_bytes()),
            (0, format!("{said}\n")),
            "{input}"
        );
    }
}

/// A float read from what a program is handed, which nothing works out
/// before it runs: the comparisons parsing a decimal answers with meet
/// wherever they join.
#[test]
fn a_float_is_read_from_standard_input() {
    let package = Package::new(
        "float-input",
        "main!(host) -> host.run_stdin!(app)

         app : {stdin: List(U8), *} -> Str
         app(input) ->
           text = Str.from_utf8(input.stdin).ok_or(\"\")
           read(F64.from_str(text.trim()))

         read : Result(F64, [Malformed]) -> Str
         read(Ok(x)) -> x.mul(2.0).to_str()
         read(Err(Malformed)) -> \"err\"",
    );
    for (input, said) in [("1.25", "2.5\n"), ("x", "err\n")] {
        assert_eq!(
            support::run_file(&package.entry(), input.as_bytes()),
            (0, said.to_owned()),
            "{input}"
        );
    }
}

/// `F32` and `F64` keep the IEEE 754 contract Ori's floats state, rule by
/// rule, each expectation the host FPU's answer, built and run on this
/// machine as `faun test` does, and asked again of the standard's own
/// definitions on the reference interpreter. The definitions take several
/// times the rest of the suite, so they are asked with
/// `cargo nextest run -p faun-cli --test expectations --run-ignored only`.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
#[ignore = "longer than the rest of the suite; run with --run-ignored only"]
fn floats_keep_the_ieee_contract() {
    let floats =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../faun/examples/floats");
    for (entry, count) in [("f32.fn", 101), ("f64.fn", 71)] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_faun"))
            .arg("test")
            .arg(floats.join(entry))
            .output()
            .unwrap();
        let said = String::from_utf8(output.stdout).unwrap();
        assert!(output.status.success(), "{entry}: {said}");
        assert_eq!(said, format!("{count} expectations hold\n"), "{entry}");
        // The machine answers with its instructions; the standard's own
        // definitions must answer the same, where no instruction does.
        assert_eq!(
            support::test_file_by_definitions(&floats.join(entry)),
            (Vec::new(), count),
            "{entry} by its definitions"
        );
    }
}
