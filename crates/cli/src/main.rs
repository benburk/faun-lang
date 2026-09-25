//! The `faun` command: check, build, run, test, or print a stage of a Faun
//! program for one of the targets this binary holds.
//!
//! This crate only parses arguments, knows which targets exist, and writes
//! what the compiler makes. The compiler itself is the `faun` library.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use bpaf::{OptionParser, Parser, choice, construct, long, positional, short};
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

#[derive(Clone, Debug)]
enum Command {
    Check {
        target: &'static dyn Target,
        source: PathBuf,
    },
    Build {
        target: &'static dyn Target,
        source: PathBuf,
        output: PathBuf,
    },
    Run {
        target: &'static dyn Target,
        source: PathBuf,
        /// What the program is run with, after its own name.
        args: Vec<String>,
    },
    Test {
        target: &'static dyn Target,
        source: PathBuf,
    },
    Emit {
        target: &'static dyn Target,
        stage: Stage,
        source: PathBuf,
    },
}

/// An intermediate stage `emit` prints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stage {
    Barb,
    Machine,
    /// The target's own rendering of what it encodes.
    Target,
}

fn main() -> ExitCode {
    let command = cli().run();
    let outcome = dispatch(command);
    match outcome {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("faun: {error}");
            ExitCode::FAILURE
        }
    }
}

/// `--target`, defaulting to [`NATIVE`] and required where there is none.
fn target_parser() -> impl Parser<&'static dyn Target> {
    long("target")
        .help("Machine to compile for")
        .argument::<String>("TARGET")
        .parse(|name| {
            TARGETS
                .into_iter()
                .find(|target| target.name() == name)
                .ok_or_else(|| unknown_target(&name))
        })
        .fallback_with(|| NATIVE.ok_or(NO_NATIVE))
        .debug_fallback()
}

fn build_parser() -> impl Parser<Command> {
    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file to compile");
    let output = short('o')
        .long("output")
        .help("Where to write artifacts")
        .argument::<PathBuf>("PATH")
        .fallback(PathBuf::from("a.out"))
        .debug_fallback();
    construct!(Command::Build {
        output,
        target,
        source,
    })
    .to_options()
    .descr("Compile a Faun program")
    .command("build")
}

fn emit_parser() -> impl Parser<Command> {
    let target = target_parser();
    let stage = positional::<String>("STAGE")
        .help("The stage to print: barb, machine or target")
        .parse(|stage| match stage.as_str() {
            "barb" => Ok(Stage::Barb),
            "machine" => Ok(Stage::Machine),
            "target" => Ok(Stage::Target),
            _ => Err("expected barb, machine or target"),
        });
    let source = positional::<PathBuf>("PATH").help("The source file to compile");
    construct!(Command::Emit {
        target,
        stage,
        source,
    })
    .to_options()
    .descr("Print an intermediate stage of a Faun program")
    .command("emit")
}

fn cli() -> OptionParser<Command> {
    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    let check = construct!(Command::Check { target, source })
        .to_options()
        .descr("Check a Faun program against the selected machine's host")
        .command("check");

    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file to compile and run");
    let args = positional::<String>("ARGS")
        .help("What the program is run with; after `--`, even what looks like an option")
        .many();
    let run = construct!(Command::Run {
        target,
        source,
        args
    })
    .to_options()
    .descr("Compile a Faun program for the selected machine and run it")
    .command("run");

    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file whose package to test");
    let test = construct!(Command::Test { target, source })
        .to_options()
        .descr("Run every `expect` in a Faun package on the selected machine")
        .command("test");

    choice([
        check.boxed(),
        build_parser().boxed(),
        run.boxed(),
        test.boxed(),
        emit_parser().boxed(),
    ])
    .to_options()
    .descr("The Faun compiler")
    .version(env!("CARGO_PKG_VERSION"))
}

const NO_NATIVE: &str = "no target runs on this machine, so --target is required";

fn unknown_target(name: &str) -> String {
    let known = TARGETS
        .iter()
        .map(|target| target.name())
        .collect::<Vec<_>>()
        .join(", ");
    format!("unknown target `{name}`, expected: {known}")
}

fn dispatch(command: Command) -> Result<(), String> {
    match command {
        Command::Check { source, target } => check(&source, target),
        Command::Build {
            source,
            output,
            target,
        } => build(&source, target, &output),
        Command::Run {
            source,
            target,
            args,
        } => run(&source, target, &args),
        Command::Test { source, target } => test(&source, target),
        Command::Emit {
            target,
            stage,
            source,
        } => emit(stage, &source, target),
    }
}

/// Check a package against the target's host by lowering it as far as Barb.
fn check(source: &Path, target: &dyn Target) -> Result<(), String> {
    faun::lower_to_barb(source, target)?;
    Ok(())
}

/// Compile an application and write its image to `output`. A library has
/// nothing to build, so building one checks it.
fn build(source: &Path, target: &dyn Target, output: &Path) -> Result<(), String> {
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

/// Compile for the machine this runs on, run it, and exit as it did.
fn run(source: &Path, target: &dyn Target, args: &[String]) -> Result<(), String> {
    runs_here(target)?;
    let image = faun::compile_to_image(source, target)?;
    let status = execute(target, &image, |program| {
        Process::new(program)
            .args(args)
            .status()
            .map_err(|error| format!("cannot run {}: {error}", program.display()))
    })?;
    std::process::exit(status.code().unwrap_or(1))
}

/// Build a package's expectations for the machine this runs on, run them,
/// and say where each one that does not hold was written.
fn test(source: &Path, target: &dyn Target) -> Result<(), String> {
    runs_here(target)?;
    let tests = faun::lower_tests_to_barb(source, target)?;
    let count = tests.expectations.len();
    if count == 0 {
        println!("no expectations");
        return Ok(());
    }
    let image = faun::compile_barb_to_image(tests.barb, target)?;
    let output = execute(target, &image, |program| {
        Process::new(program)
            .output()
            .map_err(|error| format!("cannot run {}: {error}", program.display()))
    })?;
    if !output.status.success() {
        return Err(format!("the expectations stopped with {}", output.status));
    }
    let failed = String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .map(|number| {
            number
                .parse::<usize>()
                .ok()
                .and_then(|number| tests.expectations.get(number.checked_sub(1)?))
                .ok_or_else(|| format!("the expectations answered `{number}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    report(&failed, count)
}

/// Say where each expectation that failed was written, and how many of
/// `count` held: an error where any failed.
fn report(failed: &[&faun::diagnostic::Location], count: usize) -> Result<(), String> {
    for location in failed {
        println!(
            "{}:{}: does not hold: {}",
            location.path.display(),
            location.line,
            location.text.trim()
        );
    }
    let counted = if count == 1 {
        "1 expectation".to_owned()
    } else {
        format!("{count} expectations")
    };
    match failed.len() {
        0 if count == 1 => println!("{counted} holds"),
        0 => println!("{counted} hold"),
        1 => return Err(format!("1 of {counted} does not hold")),
        n => return Err(format!("{n} of {counted} do not hold")),
    }
    Ok(())
}

/// Refuse a target whose programs this machine cannot run.
fn runs_here(target: &dyn Target) -> Result<(), String> {
    if NATIVE.is_none_or(|native| native.name() != target.name()) {
        return Err(format!(
            "{} programs do not run on this machine",
            target.name()
        ));
    }
    Ok(())
}

/// Write `image` to a directory of its own, `start` it there, and remove the
/// directory whatever it did.
fn execute<T>(
    target: &dyn Target,
    image: &[u8],
    start: impl FnOnce(&Path) -> Result<T, String>,
) -> Result<T, String> {
    let directory = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
    fs::create_dir_all(&directory)
        .map_err(|error| format!("cannot create {}: {error}", directory.display()))?;
    let outcome =
        write(target, image, &directory.join("program")).and_then(|program| start(&program));
    fs::remove_dir_all(&directory)
        .map_err(|error| format!("cannot remove {}: {error}", directory.display()))?;
    outcome
}

/// Print one stage of a program.
fn emit(stage: Stage, source: &Path, target: &dyn Target) -> Result<(), String> {
    let mut barb = faun::lower_to_barb(source, target)?;
    barb::optimize(&mut barb);
    let text = match stage {
        Stage::Barb => barb.render(),
        Stage::Machine => faun_core::lower_to_machine_ir(&mut barb, &target.routines())?.render(),
        Stage::Target => {
            let machine = faun_core::lower_to_machine_ir(&mut barb, &target.routines())?;
            target.render(&target.prepare(&machine)?)
        }
    };
    print!("{text}");
    Ok(())
}

/// Write an image through its target, answering the path written.
fn write(target: &dyn Target, image: &[u8], output: &Path) -> Result<PathBuf, String> {
    target
        .write(image, output)
        .map_err(|error| format!("cannot write {}: {error}", output.display()))
}
