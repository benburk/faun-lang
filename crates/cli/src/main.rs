//! The Faun compiler's command line: check, build, run, or print a stage of
//! a Faun program for one of the targets this binary holds.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use bpaf::{OptionParser, Parser, choice, construct, long, positional, short};
use faun_core::targets::Target;
use faun_core::{barb, ir};
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
    let run = construct!(Command::Run { target, source })
        .to_options()
        .descr("Compile a Faun program for the selected machine and run it")
        .command("run");

    choice([
        check.boxed(),
        build_parser().boxed(),
        run.boxed(),
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
        Command::Run { source, target } => run(&source, target),
        Command::Emit {
            target,
            stage,
            source,
        } => emit(stage, &source, target),
    }
}

/// Check a program by lowering it as far as Barb.
fn check(source: &Path, target: &dyn Target) -> Result<(), String> {
    faun::lower(source, target)?;
    Ok(())
}

/// Compile a program and write its image to `output`.
fn build(source: &Path, target: &dyn Target, output: &Path) -> Result<(), String> {
    let machine = lower(source, target)?;
    let image = target.compile(&machine)?;
    let written = write(target, &image, output)?;
    println!("wrote {}", written.display());
    Ok(())
}

/// Compile for the machine this runs on, run it, and exit as it did.
fn run(source: &Path, target: &dyn Target) -> Result<(), String> {
    if NATIVE.is_none_or(|native| native.name() != target.name()) {
        return Err(format!(
            "{} programs do not run on this machine",
            target.name()
        ));
    }
    let machine = lower(source, target)?;
    let image = target.compile(&machine)?;
    let directory = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
    fs::create_dir_all(&directory)
        .map_err(|error| format!("cannot create {}: {error}", directory.display()))?;
    let status = write(target, &image, &directory.join("program")).and_then(|program| {
        Process::new(&program)
            .status()
            .map_err(|error| format!("cannot run {}: {error}", program.display()))
    });
    fs::remove_dir_all(&directory)
        .map_err(|error| format!("cannot remove {}: {error}", directory.display()))?;
    std::process::exit(status?.code().unwrap_or(1))
}

/// Print one stage of a program.
fn emit(stage: Stage, source: &Path, target: &dyn Target) -> Result<(), String> {
    let text = match stage {
        Stage::Barb => {
            let mut barb = faun::lower(source, target)?;
            barb::optimize(&mut barb);
            barb.render()
        }
        Stage::Machine => lower(source, target)?.render(),
        Stage::Target => {
            let machine = lower(source, target)?;
            let prepared = target.prepare(&machine)?;
            target.render(&prepared)
        }
    };
    print!("{text}");
    Ok(())
}

/// Lower a program to the machine IR `target` compiles: to Barb, optimized,
/// then to machine IR.
fn lower(source: &Path, target: &dyn Target) -> Result<ir::Program, String> {
    let mut barb = faun::lower(source, target)?;
    barb::optimize(&mut barb);
    let machine = faun_core::lower(&mut barb, &target.routines())?;
    Ok(machine)
}

/// Write an image through its target, answering the path written.
fn write(target: &dyn Target, image: &[u8], output: &Path) -> Result<PathBuf, String> {
    target
        .write(image, output)
        .map_err(|error| format!("cannot write {}: {error}", output.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emit_prints_intermediate_stages_for_any_target() {
        let barb = cli()
            .run_inner(&["emit", "--target", "wasm32-wasi", "barb", "example.fn"])
            .unwrap();
        assert!(matches!(
            barb,
            Command::Emit {
                target,
                stage: Stage::Barb,
                source,
            } if target.name() == "wasm32-wasi" && source == Path::new("example.fn")
        ));

        let machine = cli()
            .run_inner(&["emit", "--target", "mos6502-sim65", "machine", "example.fn"])
            .unwrap();
        assert!(matches!(
            machine,
            Command::Emit {
                stage: Stage::Machine,
                ..
            }
        ));
    }

    #[test]
    fn check_selects_a_target_like_build() {
        let command = cli()
            .run_inner(&["check", "--target", "mos6502-sim65", "example.fn"])
            .unwrap();
        assert!(matches!(
            command,
            Command::Check { target, .. } if target.name() == "mos6502-sim65"
        ));
        let defaulted = cli().run_inner(&["check", "example.fn"]);
        match NATIVE {
            Some(native) => assert!(matches!(
                defaulted,
                Ok(Command::Check { target, .. }) if target.name() == native.name()
            )),
            None => assert!(defaulted.is_err()),
        }
    }

    #[test]
    fn emit_prints_the_target_rendering() {
        let command = cli()
            .run_inner(&["emit", "--target", "mos6502-sim65", "target", "example.fn"])
            .unwrap();
        assert!(matches!(
            command,
            Command::Emit {
                stage: Stage::Target,
                ..
            }
        ));
    }

    #[test]
    fn run_refuses_a_target_this_machine_does_not_run() {
        let command = cli()
            .run_inner(&["run", "--target", "wasm32-wasi", "example.fn"])
            .unwrap();
        let error = dispatch(command).unwrap_err();
        assert!(error.contains("do not run on this machine"), "{error}");
    }

    #[test]
    fn emit_rejects_unknown_stages() {
        let error = cli()
            .run_inner(&["emit", "ir", "example.fn"])
            .unwrap_err()
            .unwrap_stderr();
        assert!(
            error.contains("expected barb, machine or target"),
            "{error}"
        );
    }

    #[test]
    fn build_writes_to_a_out_unless_told_otherwise() {
        let defaulted = cli()
            .run_inner(&["build", "--target", "wasm32-wasi", "example.fn"])
            .unwrap();
        assert!(matches!(
            defaulted,
            Command::Build { output, .. } if output == Path::new("a.out")
        ));
        let named = cli()
            .run_inner(&[
                "build",
                "--target",
                "wasm32-wasi",
                "-o",
                "hello",
                "example.fn",
            ])
            .unwrap();
        assert!(matches!(
            named,
            Command::Build { output, .. } if output == Path::new("hello")
        ));
    }

    #[test]
    fn unknown_targets_name_every_target_held() {
        let error = cli()
            .run_inner(&["build", "--target", "other", "example.fn"])
            .unwrap_err()
            .unwrap_stderr();
        for target in TARGETS {
            assert!(error.contains(target.name()), "{error}");
        }
    }

    #[test]
    fn target_names_are_distinct() {
        for (at, target) in TARGETS.iter().enumerate() {
            assert!(
                TARGETS[..at]
                    .iter()
                    .all(|earlier| earlier.name() != target.name())
            );
        }
    }
}
