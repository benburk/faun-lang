//! `expect`: what a package claims of its definitions, which `faun test`
//! asks, and which checking a package checks whether or not it is asked.

mod support;

use std::fs;

use faun_x86_64_linux::X86_64Linux;
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
           doubled = [1 2 3].map(double)
           doubled.len() == 3
             & doubled.last().ok_or(0) == 6

         main!(host) -> host.exit!(9)",
    );
    fs::write(
        package.entry().with_file_name("halves.fn"),
        "exports {half}\n\nhalf : Nat -> Nat\nhalf(n) -> n / 2\n\nexpect half(7) == 3\nexpect half(1) == 1\n",
    )
    .unwrap();

    let (failed, count) = support::test_file(&package.entry());
    assert_eq!(count, 5);
    assert_eq!(failed, ["main.fn:9", "halves.fn:7"]);
    // Built as an application, the package is its own `main!`.
    assert_eq!(package.run(), 9);
}

#[test]
fn a_package_without_expectations_has_nothing_to_ask() {
    let package = Package::new("no-expectations", "main!(host) -> host.exit!(0)");
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 0));
}

/// An expectation is checked as any definition is, when the package is.
#[test]
fn an_expectation_is_checked_whether_or_not_it_is_asked() {
    for (source, refused) in [
        ("expect 3", "a numeral cannot be a `Bool`"),
        (
            "spin : Nat -> Nat\nspin(n) -> spin(n)\n\nexpect spin(1) == 1",
            "nothing here shows `spin` stops",
        ),
    ] {
        let package = Package::new("refused-expectation", source);
        let error = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap_err();
        assert!(error.message.contains(refused), "{}", error.message);
    }
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
        "package {}\n\nexports {double_square}\n\ndouble_square : Nat -> Nat\ndouble_square(n) -> n * n * 2\n\nexpect double_square(0) == 1\n",
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
         third() -> F32.div(1.0 3.0)

         expect 0.1.add(0.2).to_str() == \"0.30000000000000004\"
         expect F32.add(0.1 0.2) == 0.3
         expect third().to_str() == \"0.33333334\"
         expect (-2.5).to_str() == \"-2.5\" & 2.5E2 == 250.0 & 1.0e-12.to_str() == \"1.0e-12\"
         expect F64.from_str(\"0.1\") == Ok(0.1) & F32.from_str(\"1e\") == Err(Malformed)
         expect F32.sqrt(2.0).to_bits() == 0x3fb504f3 & F32.nan() == F32.nan()",
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 6));
}

/// `F32` and `F64` keep the IEEE 754 contract Ori's floats state, rule by
/// rule, each expectation the host FPU's answer, built and run on this
/// machine as `faun test` does, and asked again of the standard's own
/// definitions on the reference interpreter. The definitions take the
/// release build minutes, so they are asked with
/// `cargo test --release -p faun-cli --test expectations -- --ignored`.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
#[ignore = "minutes even in a release build; run with --release -- --ignored"]
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
