//! The `faun` command: check, build, run, test, or print a stage of a Faun
//! program for one of the targets this binary holds.
//!
//! This crate only parses arguments, knows which targets exist, and writes
//! what the compiler makes. The compiler itself is the `faun-frontend`
//! library and the backends it hands Barb to.

mod args;
mod bundle;
mod compiler;
mod fetch;

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use args::{Command, Stage};
use compiler::Compiler;
use faun_aarch64_macos::Aarch64Macos;
use faun_core::targets::{Favour, SymbolTable, Target};
use faun_frontend::diagnostic::Diagnostic;
use faun_frontend::packages::Packages;
use faun_frontend::{Failure, Reporting, Side};
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;
use fetch::Fetcher;

/// The compiler allocates and frees many small nodes, symbols and tables, a
/// tree at a time, and mimalloc does it in fewer instructions than the
/// system's allocator: a seventh fewer for the whole compile. Its
/// transparent huge pages are off, since on a busy machine the kernel spends
/// longer compacting memory for them than the compile takes.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Every target this binary compiles for.
const TARGETS: [&dyn Target; 4] = [&X86_64Linux, &Wasm32Wasi, &Mos6502Sim65, &Aarch64Macos];

/// The target running on this machine, which `--target` defaults to.
const NATIVE: Option<&dyn Target> = if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
    Some(&X86_64Linux)
} else if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
    Some(&Aarch64Macos)
} else {
    None
};

/// How deep the compiler may recurse. Its passes walk a program as written,
/// so a program nested thousands deep is walked as deep; the main thread's
/// few megabytes would end that in a crash. The space is only reserved:
/// what recursion never reaches is never used.
const STACK: usize = 512 << 20;

/// The built-in standard library, checked when this binary was built.
static STANDARD: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/standard.snapshot"));

fn main() -> ExitCode {
    faun_frontend::use_standard_snapshot(STANDARD);
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
            compiler,
            source,
            output,
            favour,
            symbols,
        } => build(&source, compiler, &output, favour, symbols).map(|()| ExitCode::SUCCESS),
        Command::Run {
            compiler,
            source,
            args,
        } => run(&source, compiler, &args),
        Command::Test { compiler, source } => test(&source, compiler).map(|()| ExitCode::SUCCESS),
        Command::Emit {
            compiler,
            stage,
            source,
        } => emit(stage, &source, compiler).map(|()| ExitCode::SUCCESS),
        Command::Bundle {
            target,
            source,
            output,
        } => bundle::bundle(&source, &output, target).map(|written| {
            println!("wrote {}", written.display());
            ExitCode::SUCCESS
        }),
        Command::Fetch { source } => fetch(&source).map(|()| ExitCode::SUCCESS),
        Command::Uses { source } => uses(&source).map(|()| ExitCode::SUCCESS),
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

/// Check a package against the target's host: a library by the frontend
/// alone, an application by lowering it as far as Barb.
fn check(source: &Path, target: &dyn Target) -> Result<(), Diagnostic> {
    faun_frontend::check_package_using(source, &faun_driver::platform(target), &fetched(source)?)?;
    println!("checked {}", source.display());
    Ok(())
}

/// Compile an application and write its image to `output`, favouring speed
/// or size, with symbols where `symbols` asks. A library has nothing to
/// build, so building one checks it.
fn build(
    source: &Path,
    compiler: Compiler,
    output: &Path,
    favour: Favour,
    symbols: SymbolTable,
) -> Result<(), Diagnostic> {
    let target = compiler.host();
    let faun_frontend::Package::Application(barb) =
        faun_frontend::check_package_using(source, &compiler.platform(), &fetched(source)?)?
    else {
        println!(
            "checked {}, a library with no `main!` to build",
            source.display()
        );
        return Ok(());
    };
    let image = compiler.compile(*barb, favour, symbols)?;
    let written = write(target, &image, output)?;
    println!("wrote {}", written.display());
    Ok(())
}

/// Compile for the machine this runs on, run it, and answer how it exited.
/// Where a signal stopped it, say which, and answer as a shell does,
/// 128 and the signal's number.
fn run(source: &Path, compiler: Compiler, args: &[String]) -> Result<ExitCode, Diagnostic> {
    let target = compiler.host();
    let runner = runner(target)?;
    let image = compiler.compile(
        faun_frontend::lower_to_barb_using(source, &compiler.platform(), &fetched(source)?)?,
        Favour::Speed,
        SymbolTable::Omitted,
    )?;
    let status = execute(target, runner, &image, |program| {
        program.args(args).status()
    })?;
    if let Some(signal) = stopping_signal(status) {
        eprintln!("the program was stopped by signal {signal}");
        let shell = 128 + signal;
        let byte = u8::try_from(shell).unwrap_or(u8::MAX);
        return Ok(ExitCode::from(byte));
    }
    let code = status.code();
    let byte = code.and_then(|code| u8::try_from(code).ok());
    let exit = byte.map_or(ExitCode::FAILURE, ExitCode::from);
    Ok(exit)
}

/// The signal that stopped a program, where one did.
#[cfg(unix)]
fn stopping_signal(status: std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    status.signal()
}

#[cfg(not(unix))]
fn stopping_signal(_status: std::process::ExitStatus) -> Option<i32> {
    None
}

/// Build a package's expectations for the machine this runs on, run them,
/// and say where each one that does not hold was written, and what each
/// comparison among them saw.
fn test(source: &Path, compiler: Compiler) -> Result<(), Diagnostic> {
    let target = compiler.host();
    let runner = runner(target)?;
    let packages = fetched(source)?;
    let mut tests = faun_frontend::lower_tests_to_barb_using(
        source,
        &compiler.platform(),
        &packages,
        Reporting::Each,
    )?;
    let count = tests.expectations.len();
    if count == 0 {
        println!("no expectations");
        return Ok(());
    }
    let barb = std::mem::take(&mut tests.barb);
    let image = compiler.compile(barb, Favour::Speed, SymbolTable::Omitted)?;
    let output = execute(target, runner, &image, Process::output)?;
    let answered = tests.answered(&output.stdout).map_err(Diagnostic::new)?;
    if !output.status.success() {
        tell_failures(&answered.failed);
        // Each record is printed as its expectation is asked, so the one
        // after the last is the one that stopped.
        let message = format!("the expectations stopped with {}", output.status);
        let stopped = Diagnostic::new(message);
        return Err(match tests.expectations.get(answered.asked) {
            Some(location) => stopped
                .at_location(location.clone())
                .note("this expectation was being asked"),
            None => stopped,
        });
    }
    report(&answered.failed, count)
}

/// Tell each expectation that failed, with what each comparison saw.
fn tell_failures(failed: &[Failure<'_>]) {
    for failure in failed {
        let diagnostic = Diagnostic::new("this expectation does not hold");
        let mut diagnostic = diagnostic.at_location(failure.location.clone());
        match &failure.sides {
            Some((Side::Shown(left), Side::Shown(right))) => {
                diagnostic = diagnostic
                    .note(format!("left:  {left}"))
                    .note(format!("right: {right}"));
            }
            Some((Side::Unshown(ty), _) | (_, Side::Unshown(ty))) => {
                diagnostic =
                    diagnostic.note(format!("neither side is shown: `{ty}` has no `to_str`"));
            }
            None => {}
        }
        tell(diagnostic);
        eprintln!();
    }
}

/// Tell each expectation that failed, and how many of `count` held: an
/// error where any failed.
fn report(failed: &[Failure<'_>], count: usize) -> Result<(), Diagnostic> {
    tell_failures(failed);
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

/// A runtime and its options, or an empty command for native execution.
fn runner(target: &dyn Target) -> Result<&'static [&'static str], Diagnostic> {
    if NATIVE.is_some_and(|native| native.name() == target.name()) {
        return Ok(&[]);
    }
    match target.name() {
        "wasm32-wasi" => Ok(&["wasmtime", "run", "--dir", "."]),
        "mos6502-sim65" => Ok(&["sim65"]),
        name => Err(
            Diagnostic::new(format!("{name} programs do not run on this machine"))
                .help(format!("cross-compile with `faun build --target {name}`")),
        ),
    }
}

/// Write `image` to a directory of its own, `start` it there, and remove the
/// directory whatever it did.
fn execute<T>(
    target: &dyn Target,
    runner: &[&str],
    image: &[u8],
    start: impl FnOnce(&mut Process) -> io::Result<T>,
) -> Result<T, Diagnostic> {
    let directory = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
    fs::create_dir_all(&directory).map_err(|error| cannot("create", &directory, &error))?;
    let outcome = write(target, image, &directory.join("program")).and_then(|program| {
        let (command, options) = runner
            .split_first()
            .map_or((program.as_path(), &[][..]), |(bin, flags)| {
                (Path::new(bin), flags)
            });
        let mut process = Process::new(command);
        if !runner.is_empty() {
            process.args(options).arg(&program);
        }
        start(&mut process).map_err(|error| cannot("run", command, &error))
    });
    fs::remove_dir_all(&directory).map_err(|error| cannot("remove", &directory, &error))?;
    outcome
}

/// Print one stage of a program.
fn emit(stage: Stage, source: &Path, compiler: Compiler) -> Result<(), Diagnostic> {
    let mut barb =
        faun_frontend::lower_to_barb_using(source, &compiler.platform(), &fetched(source)?)?;
    barb::optimize(&mut barb);
    let text = compiler.render(stage, &barb).map_err(Diagnostic::new)?;
    print!("{text}");
    Ok(())
}

/// Every URL dependency of the package at `source`, fetched where it is not
/// cached, with the version each is read at.
fn fetched(source: &Path) -> Result<Packages, Diagnostic> {
    Fetcher::new()?.resolve(source)
}

/// Fetch every URL dependency of the package at `source`, and say how many
/// were downloaded.
fn fetch(source: &Path) -> Result<(), Diagnostic> {
    let mut fetcher = Fetcher::new()?;
    let packages = fetcher.resolve(source)?;
    let urls = packages
        .tree
        .iter()
        .filter(|used| !used.shown && faun_frontend::packages::PackageUrl::is_url(&used.written))
        .count();
    println!("{urls} URL dependencies, {} downloaded", fetcher.downloaded);
    Ok(())
}

/// Print the packages the package at `source` uses, as a tree: each by the
/// URL or path its header wrote, with the version chosen in its place where
/// one was, and marked where it was shown before.
fn uses(source: &Path) -> Result<(), Diagnostic> {
    let packages = fetched(source)?;
    println!("{}", source.display());
    for used in &packages.tree {
        let indent = "  ".repeat(used.depth + 1);
        let tests = if used.for_tests { " (tests)" } else { "" };
        let chosen = used
            .chosen
            .map(|version| format!(" (uses {version})"))
            .unwrap_or_default();
        let shown = if used.shown { " (shown above)" } else { "" };
        println!(
            "{indent}{}: {}{tests}{chosen}{shown}",
            used.name, used.written
        );
    }
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
