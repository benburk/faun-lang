//! The `faun` command: check, build, run, test, or print a stage of a Faun
//! program for one of the targets this binary holds.
//!
//! This crate only parses arguments, knows which targets exist, and writes
//! what the compiler makes. The compiler itself is the `faun` library.

mod args;

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use args::{Command, Stage};
use faun::diagnostic::{Diagnostic, Location};
use faun_core::barb;
use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

/// Every target this binary compiles for.
const TARGETS: [&dyn Target; 3] = [&X86_64Linux, &Wasm32Wasi, &Mos6502Sim65];

/// The target running on this machine, which `--target` defaults to.
const NATIVE: Option<&dyn Target> = if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
    Some(&X86_64Linux)
} else {
    None
};

/// How deep the compiler may recurse. Its passes walk a program as written,
/// so a program nested thousands deep is walked as deep; the main thread's
/// few megabytes would end that in a crash. The space is only reserved:
/// what recursion never reaches is never used.
const STACK: usize = 512 << 20;

fn main() -> ExitCode {
    std::thread::Builder::new()
        .name("faun".to_owned())
        .stack_size(STACK)
        .spawn(|| answer(args::parse()))
        .expect("the compiler's thread starts")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

/// Do what `command` says, and say what went wrong where anything did.
fn answer(command: Command) -> ExitCode {
    let outcome = match command {
        Command::Check { target, source } => check(&source, target).map(|()| ExitCode::SUCCESS),
        Command::Build {
            target,
            source,
            output,
        } => build(&source, target, &output).map(|()| ExitCode::SUCCESS),
        Command::Run {
            target,
            source,
            args,
        } => run(&source, target, &args),
        Command::Test { target, source } => test(&source, target).map(|()| ExitCode::SUCCESS),
        Command::Emit {
            target,
            stage,
            source,
        } => emit(stage, &source, target).map(|()| ExitCode::SUCCESS),
    };
    match outcome {
        Ok(exit) => exit,
        Err(diagnostic) => {
            tell(diagnostic);
            ExitCode::FAILURE
        }
    }
}

/// Write a diagnostic to standard error, its paths shown from where this
/// runs, as they were given.
fn tell(diagnostic: Diagnostic) {
    let here = std::env::current_dir().and_then(fs::canonicalize);
    let diagnostic = match here {
        Ok(here) => diagnostic.relative_to(&here),
        Err(_) => diagnostic,
    };
    eprintln!("{diagnostic}");
}

/// Check a package against the target's host by lowering it as far as Barb.
fn check(source: &Path, target: &dyn Target) -> Result<(), Diagnostic> {
    faun::lower_to_barb(source, target)?;
    println!("checked {}", source.display());
    Ok(())
}

/// Compile an application and write its image to `output`. A library has
/// nothing to build, so building one checks it.
fn build(source: &Path, target: &dyn Target, output: &Path) -> Result<(), Diagnostic> {
    let barb = faun::lower_to_barb(source, target)?;
    if barb.entry().is_none() {
        println!(
            "checked {}, a library with no `main!` to build",
            source.display()
        );
        return Ok(());
    }
    let image = faun::compile_barb_to_image(barb, target)?;
    let written = write(target, &image, output)?;
    println!("wrote {}", written.display());
    Ok(())
}

/// Compile for the machine this runs on, run it, and answer how it exited:
/// failure where a signal stopped it.
fn run(source: &Path, target: &dyn Target, args: &[String]) -> Result<ExitCode, Diagnostic> {
    runs_here(target)?;
    let image = faun::compile_to_image(source, target)?;
    let status = execute(target, &image, |program| program.args(args).status())?;
    let code = status.code();
    let byte = code.and_then(|code| u8::try_from(code).ok());
    let exit = byte.map_or(ExitCode::FAILURE, ExitCode::from);
    Ok(exit)
}

/// Build a package's expectations for the machine this runs on, run them,
/// and say where each one that does not hold was written.
fn test(source: &Path, target: &dyn Target) -> Result<(), Diagnostic> {
    runs_here(target)?;
    let tests = faun::lower_tests_to_barb(source, target)?;
    let count = tests.expectations.len();
    if count == 0 {
        println!("no expectations");
        return Ok(());
    }
    let image = faun::compile_barb_to_image(tests.barb, target)?;
    let output = execute(target, &image, Process::output)?;
    if !output.status.success() {
        let message = format!("the expectations stopped with {}", output.status);
        return Err(Diagnostic::new(message));
    }
    let answered = String::from_utf8_lossy(&output.stdout);
    let failed = failed(&answered, &tests.expectations)?;
    report(&failed, count)
}

/// Where each expectation the test build `answered` as failing was written.
fn failed<'a>(
    answered: &str,
    expectations: &'a [Location],
) -> Result<Vec<&'a Location>, Diagnostic> {
    let mut failed = Vec::new();
    for number in answered.split_whitespace() {
        let parsed = number.parse::<usize>().ok();
        let index = parsed.and_then(|parsed| parsed.checked_sub(1));
        let location = index.and_then(|index| expectations.get(index));
        let Some(location) = location else {
            let message = format!("the expectations answered `{number}`");
            return Err(Diagnostic::new(message));
        };
        failed.push(location);
    }
    Ok(failed)
}

/// Tell each expectation that failed, and how many of `count` held: an
/// error where any failed.
fn report(failed: &[&Location], count: usize) -> Result<(), Diagnostic> {
    for &location in failed {
        let diagnostic = Diagnostic::new("this expectation does not hold");
        let diagnostic = diagnostic.at_location(location.clone());
        tell(diagnostic);
        eprintln!();
    }
    let counted = if count == 1 {
        "1 expectation".to_owned()
    } else {
        format!("{count} expectations")
    };
    let failures = failed.len();
    if failures == 0 {
        let verb = if count == 1 { "holds" } else { "hold" };
        println!("{counted} {verb}");
        return Ok(());
    }
    let verb = if failures == 1 { "does" } else { "do" };
    let message = format!("{failures} of {counted} {verb} not hold");
    Err(Diagnostic::new(message))
}

/// Refuse a target whose programs this machine cannot run.
fn runs_here(target: &dyn Target) -> Result<(), Diagnostic> {
    let name = target.name();
    if NATIVE.is_none_or(|native| native.name() != name) {
        let diagnostic = Diagnostic::new(format!("{name} programs do not run on this machine"));
        let diagnostic = diagnostic.help(format!(
            "build one with `faun build --target {name}` instead"
        ));
        return Err(diagnostic);
    }
    Ok(())
}

/// Write `image` to a directory of its own, `start` it there, and remove the
/// directory whatever it did.
fn execute<T>(
    target: &dyn Target,
    image: &[u8],
    start: impl FnOnce(&mut Process) -> io::Result<T>,
) -> Result<T, Diagnostic> {
    let directory = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
    fs::create_dir_all(&directory).map_err(|error| cannot("create", &directory, &error))?;
    let outcome = write(target, image, &directory.join("program")).and_then(|program| {
        let mut process = Process::new(&program);
        start(&mut process).map_err(|error| cannot("run", &program, &error))
    });
    fs::remove_dir_all(&directory).map_err(|error| cannot("remove", &directory, &error))?;
    outcome
}

/// Print one stage of a program.
fn emit(stage: Stage, source: &Path, target: &dyn Target) -> Result<(), Diagnostic> {
    let mut barb = faun::lower_to_barb(source, target)?;
    barb::optimize(&mut barb);
    let routines = target.routines();
    let text = match stage {
        Stage::Barb => barb.analyze().render(),
        Stage::Machine => {
            let machine =
                faun_core::lower_to_machine_ir(&mut barb, &routines).map_err(Diagnostic::new)?;
            machine.render()
        }
        Stage::Target => {
            let machine =
                faun_core::lower_to_machine_ir(&mut barb, &routines).map_err(Diagnostic::new)?;
            let prepared = target.prepare(&machine).map_err(Diagnostic::new)?;
            target.render(&prepared)
        }
    };
    print!("{text}");
    Ok(())
}

/// Write an image through its target, answering the path written.
fn write(target: &dyn Target, image: &[u8], output: &Path) -> Result<PathBuf, Diagnostic> {
    target
        .write(image, output)
        .map_err(|error| cannot("write", output, &error))
}

/// What the file system refused: to `act` on `path`.
fn cannot(act: &str, path: &Path, error: &io::Error) -> Diagnostic {
    Diagnostic::new(format!("cannot {act} {}: {error}", path.display()))
}
