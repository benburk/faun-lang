//! A package is checked whole: every definition it writes that can stand on
//! its own is lowered and must be total, whether or not anything calls it.
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
fn a_definition_nothing_calls_must_still_stop() {
    let spin = "spin : Nat -> Nat\nspin(n) -> spin(n)\n";
    let library = Package::new("spinning-library", spin);
    let application = Package::new(
        "spinning-application",
        &format!(
            "import std.host {{Host}}\n\n{spin}\nmain! : Host -> []\nmain!(host) -> host.exit!(0)\n"
        ),
    );
    for package in [library, application] {
        let refused = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap_err();
        assert!(
            refused.message.contains("`spin` stops"),
            "{}",
            refused.message
        );
    }
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

#[test]
fn a_definition_taking_a_function_is_compiled_where_it_is_called() {
    let package = Package::new(
        "higher-order",
        "twice : (Nat -> Nat) Nat -> Nat\ntwice(f n) -> f(f(n))\n",
    );
    let barb = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    assert!(!barb.render().contains("twice"));
}

#[test]
fn a_definition_that_may_not_stop_is_refused_at_its_looping_call() {
    let package = Package::new(
        "mutual",
        "step : Nat -> Nat\nstep(Succ(n)) -> hop(n)\nstep(Zero) -> 0\n\n\
         hop : Nat -> Nat\nhop(m) -> step(Succ(Succ(m)))\n",
    );
    let refused = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap_err();
    assert!(refused.message.contains("`step`, `hop` stops"), "{refused}");
    let at = refused.location.expect("the looping call");
    assert_eq!(
        (at.line, at.column, at.text.as_str()),
        (2, 18, "step(Succ(n)) -> hop(n)")
    );
}

#[test]
fn clauses_that_leave_a_case_unmatched_are_refused_even_when_generic() {
    for (name, source, missing) in [
        (
            "first",
            "first : List(a) -> a\nfirst([x *rest]) -> x\n",
            "first([])",
        ),
        (
            "pick",
            "pick : Bool Bool -> Nat\npick(True _) -> 0\npick(_ True) -> 1\n",
            "pick(False False)",
        ),
    ] {
        let package = Package::new(name, source);
        let refused = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap_err();
        assert!(
            refused
                .message
                .contains(&format!("no clause matches `{missing}`")),
            "{refused}"
        );
    }
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
        "length : List(a) -> Nat\nlength([]) -> 0\nlength([_ *rest]) -> 1 + length(rest)\n",
    );
    let barb = faun::lower_to_barb(&total.entry(), &X86_64Linux).unwrap();
    assert!(barb.render().contains("length(v0: List<[]>) -> Nat ="));
    let looping = Package::new(
        "loop",
        "loop : List(a) -> Nat\nloop([]) -> 0\nloop(xs) -> loop(xs)\n",
    );
    let refused = faun::lower_to_barb(&looping.entry(), &X86_64Linux).unwrap_err();
    assert!(refused.message.contains("`loop` stops"), "{refused}");
}
