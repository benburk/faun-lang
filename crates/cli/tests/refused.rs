//! Programs the compiler must refuse, and exactly what it says about each.
//!
//! Every case under `tests/refused/` is a program `faun check` refuses: a
//! file `<case>.fn`, or a directory `<case>/` whose entry is `main.fn` for a
//! case needing more than one module. Beside it, `<case>.err` holds what
//! `faun check` writes to standard error, verbatim. Comparing all of it, not
//! a phrase from it, means a diagnostic that loses its place, its caret or
//! its help is a diff rather than a test still passing.
//!
//! When a message is meant to change, run `just bless` to write every
//! `.err` again from what the compiler says now, and read the diff: that
//! review is why they are kept.
//!
//! Each case is its own test, named for its file, so one can be run alone
//! and one failing does not hide another.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use libtest_mimic::{Arguments, Failed, Trial};

fn main() {
    let arguments = Arguments::from_args();
    let directory = refused();
    let mut trials = Vec::new();
    for case in cases(&directory) {
        let name = case.name.clone();
        let trial = Trial::test(name, move || check(&case));
        trials.push(trial);
    }
    trials.push(Trial::test("every_err_file_has_its_case", move || {
        orphans(&directory)
    }));
    libtest_mimic::run(&arguments, trials).exit();
}

/// Where the cases are.
fn refused() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/refused")
}

/// A program to refuse.
struct Case {
    name: String,
    /// The entry `faun check` is given, from the cases' directory.
    entry: PathBuf,
    /// Where what it says is kept.
    golden: PathBuf,
}

/// Every case under `directory`, by name.
fn cases(directory: &Path) -> Vec<Case> {
    let mut cases = Vec::new();
    for entry in fs::read_dir(directory).expect("tests/refused is readable") {
        let path = entry.expect("tests/refused is readable").path();
        let name = path.file_stem().expect("a case has a name");
        let name = name.to_string_lossy().into_owned();
        let entry = if path.is_dir() {
            PathBuf::from(&name).join("main.fn")
        } else if path.extension().is_some_and(|extension| extension == "fn") {
            PathBuf::from(format!("{name}.fn"))
        } else {
            continue;
        };
        let golden = directory.join(format!("{name}.err"));
        cases.push(Case {
            name,
            entry,
            golden,
        });
    }
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

/// Check the case as someone would from the cases' directory, and hold
/// what it says to its `.err`.
fn check(case: &Case) -> Result<(), Failed> {
    let output = Command::new(env!("CARGO_BIN_EXE_faun"))
        .args(["check", "--target", "x86_64-linux"])
        .arg(&case.entry)
        .current_dir(refused())
        .output()
        .map_err(|error| format!("cannot run faun: {error}"))?;
    if output.status.success() {
        return Err("faun check accepted this; a refused case must be refused".into());
    }
    let told = String::from_utf8(output.stderr).map_err(|_| "faun wrote non-UTF-8")?;
    if blessing() {
        fs::write(&case.golden, &told)
            .map_err(|error| format!("cannot write {}: {error}", case.golden.display()))?;
        return Ok(());
    }
    let Ok(expected) = fs::read_to_string(&case.golden) else {
        let message = format!(
            "{} is missing; run `just bless` and read what it wrote\n\n{told}",
            case.golden.display()
        );
        return Err(message.into());
    };
    if told != expected {
        let message = format!(
            "faun check said something else.\n\n\
             --- expected ({}) ---\n{expected}\n\
             --- said ---\n{told}\n\
             If what it says now is better, run `just bless` and read the diff.",
            case.golden.display()
        );
        return Err(message.into());
    }
    Ok(())
}

/// Every `.err` belongs to a case: one left behind when its case moved or
/// was removed is a failure, not a file nobody reads.
fn orphans(directory: &Path) -> Result<(), Failed> {
    let cases = cases(directory);
    let mut orphans = Vec::new();
    for entry in fs::read_dir(directory).expect("tests/refused is readable") {
        let path = entry.expect("tests/refused is readable").path();
        if path.extension().is_none_or(|extension| extension != "err") {
            continue;
        }
        if !cases.iter().any(|case| case.golden == path) {
            orphans.push(path.display().to_string());
        }
    }
    if orphans.is_empty() {
        return Ok(());
    }
    Err(format!("no case for {}", orphans.join(", ")).into())
}

/// Whether to write each `.err` from what the compiler says now.
fn blessing() -> bool {
    std::env::var_os("FAUN_BLESS").is_some_and(|value| value != "0")
}
