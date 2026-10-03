//! A package is checked whole: every definition it writes that can stand on
//! its own is lowered and validated, whether or not anything calls it.
//! An entry defining `main!` makes it an application, whose Barb starts
//! there; without one it is a library, whose Barb has no entry and which has
//! nothing to build.

use std::fs;
use std::path::PathBuf;

use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;

/// A package written to its own directory, removed when dropped.
struct Package(PathBuf);

impl Package {
    fn new(name: &str, source: &str) -> Self {
        let directory =
            std::env::temp_dir().join(format!("faun-package-{name}-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("main.fn"), source).unwrap();
        Self(directory)
    }

    fn entry(&self) -> PathBuf {
        self.0.join("main.fn")
    }
}

impl Drop for Package {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_library_lowers_to_barb_with_no_entry_and_does_not_build() {
    let package = Package::new("library", "double : Nat -> Nat\ndouble(n) -> n + n\n");
    let barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert!(barb.entry().is_none());
    assert!(barb.render().contains("double(v0: Nat) -> Nat ="));
    let nothing_to_run =
        faun_core::lower_to_machine_ir(&mut barb.clone(), &X86_64Linux.routines()).unwrap_err();
    assert!(nothing_to_run.contains("no entry"));
    let refused = faun::compile_barb_to_image(barb, &X86_64Linux).unwrap_err();
    assert!(refused.message.contains("no `main!` to build"));
}

#[test]
fn an_application_builds_only_what_main_reaches() {
    let package = Package::new(
        "unused",
        "import std.host {Host}\n\nunused : Nat -> Nat\nunused(n) -> n * 3\n\n\
         main! : Host -> []\nmain!(host) -> host.exit!(7)\n",
    );
    let barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert!(barb.render().contains("unused(v0: Nat) -> Nat ="));
    let mut optimized = barb.clone();
    faun_core::barb::optimize(&mut optimized);
    let machine = faun_core::lower_to_machine_ir(&mut optimized, &X86_64Linux.routines()).unwrap();
    assert!(!machine.render().contains("unused"));
    faun::compile_barb_to_image(barb, &X86_64Linux).unwrap();
}

/// A loop every caller hands the same string holds the string itself, and
/// what it asks of the string is then answered before the program runs.
#[test]
fn what_a_loop_asks_of_a_value_every_caller_hands_it_is_folded() {
    let package = Package::new(
        "invariant",
        "import std.host {Host}\n\n\
         seek : (List(U8), Nat) -> Nat\n\
         seek(name, _) if name.contains(0) -> 1\n\
         seek(_, 0) -> 0\n\
         seek(name, Succ(fuel)) -> seek(name, fuel)\n\n\
         main! : Host -> []\n\
         main!(host) -> host.exit!(U8.of_nat(seek(\"a.txt\".to_utf8(), host.args.len())))\n",
    );
    let mut barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert!(barb.render().contains("List.any"));
    faun_core::barb::optimize(&mut barb);
    let rendered = barb.render();
    assert!(!rendered.contains("List.any"), "{rendered}");
}

/// Where callers hand a loop different strings, each gets a copy of the
/// loop holding its own, and what it asks of it is answered there: but only
/// where that decides which way the loop goes.
#[test]
fn a_loop_handed_different_strings_is_copied_for_each_where_that_decides_something() {
    let seek = "seek : (List(U8), Nat) -> Nat\n\
                seek(name, _) if name.contains(0) -> 1\n\
                seek(_, 0) -> 0\n\
                seek(name, Succ(fuel)) -> seek(name, fuel)\n\n\
                count : (List(U8), Nat) -> Nat\n\
                count(_, 0) -> 0\n\
                count(name, Succ(fuel)) -> name.len() + count(name, fuel)\n\n";
    let package = Package::new(
        "specialized",
        &format!(
            "import std.host {{Host}}\n\n{seek}\
             main! : Host -> []\n\
             main!(host) -> (\n  \
               n = host.args.len()\n  \
               host.exit!(U8.of_nat(seek(\"a.txt\".to_utf8(), n) + seek(\"b.txt\".to_utf8(), n) \
               + count(\"a\".to_utf8(), n) + count(\"bb\".to_utf8(), n)))\n\
             )\n"
        ),
    );
    let mut barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    faun_core::barb::optimize(&mut barb);
    let rendered = barb.render();
    assert!(!rendered.contains("List.any"), "{rendered}");
    assert!(!rendered.contains("\nseek("), "{rendered}");
    // Knowing its string decides nothing in `count`, so there is one.
    let counts = rendered
        .lines()
        .filter(|line| line.starts_with("count"))
        .count();
    assert_eq!(counts, 1, "{rendered}");
}

#[test]
fn a_definition_taking_a_function_is_compiled_where_it_is_called() {
    let package = Package::new(
        "higher-order",
        "twice : (Nat -> Nat, Nat) -> Nat\ntwice(f, n) -> f(f(n))\n",
    );
    let barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert!(!barb.render().contains("twice"));
}

/// Clauses that cover every case between them are accepted, however they
/// split them; those leaving one unmatched are in `refused/`.
#[test]
fn clauses_that_cover_every_case_are_accepted() {
    let covered = Package::new(
        "covered",
        "sign : Int -> Nat\nsign(0) -> 0\nsign(Pos(Succ(_))) -> 1\nsign(NegSucc(_)) -> 2\n",
    );
    faun::lower_to_barb(&covered.entry(), &X86_64Linux).unwrap();
}

#[test]
fn a_generic_definition_nothing_calls_is_judged_at_the_empty_type() {
    let total = Package::new(
        "length",
        "length : List(a) -> Nat\nlength([]) -> 0\nlength([_, *rest]) -> 1 + length(rest)\n",
    );
    let barb = faun::lower_to_barb(&total.entry(), &X86_64Linux).unwrap();
    assert!(barb.render().contains("length(v0: List<[]>) -> Nat ="));
}

/// A package with a library it depends on beside it, under `vendor/`.
fn with_dependency(name: &str, entry: &str) -> Package {
    let package = Package::new(name, entry);
    let vendor = package.0.join("vendor/shapes");
    fs::create_dir_all(&vendor).unwrap();
    fs::write(
        vendor.join("shapes.fn"),
        "package {}\n\nimport area {square}\n\nexport {double_square}\n\ndouble_square : Nat -> Nat\ndouble_square(n) -> square(n) * 2\n\nexpect double_square(3) == 18\n",
    )
    .unwrap();
    fs::write(
        vendor.join("area.fn"),
        "export {square}\n\nsquare : Nat -> Nat\nsquare(n) -> n * n\n",
    )
    .unwrap();
    package
}

/// A dependency's root is imported by the name the header gives it, and
/// its own modules resolve from its own root. Its expectations are its
/// package's, not the one depending on it.
#[test]
fn a_package_imports_the_root_of_one_it_depends_on() {
    let package = with_dependency(
        "dependency",
        "package {\n  shapes: \"vendor/shapes/shapes\",\n}\n\nimport shapes {double_square}\n\neight : Nat\neight = double_square(2)\n\nexpect eight == 8\n",
    );
    faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    let tests = faun::lower_tests_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert_eq!(tests.expectations.len(), 1);
}
