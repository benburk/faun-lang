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
