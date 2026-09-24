//! The Faun compiler's command line: check, build and run a Faun program for
//! one of the targets this binary holds.

use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use bpaf::{OptionParser, Parser, choice, construct, long, positional, short};
use faun_core::targets::{Artifact, Target};
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

// Parsing constructs many short-lived AST vectors and boxes. Keeping the
// allocator optimized in development builds matters as much as optimizing the
// parser itself; the system allocator made the mixed benchmark about 20% slower.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
        target: Option<&'static dyn Target>,
        source: PathBuf,
    },
    Build {
        target: &'static dyn Target,
        source: PathBuf,
        output: Option<PathBuf>,
        emit: Option<Emit>,
    },
    Run {
        target: &'static dyn Target,
        source: PathBuf,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Emit {
    Barb,
    Machine,
}

fn main() -> ExitCode {
    match dispatch(cli().run()) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("faun: {error}");
            ExitCode::FAILURE
        }
    }
}

fn selected_target() -> impl Parser<&'static dyn Target> {
    long("target")
        .help("Machine to compile for")
        .argument::<String>("TARGET")
        .parse(|name| {
            TARGETS
                .into_iter()
                .find(|target| target.name() == name)
                .ok_or_else(|| unknown_target(&name))
        })
}

fn target_parser() -> impl Parser<&'static dyn Target> {
    selected_target()
        .fallback_with(|| NATIVE.ok_or(NO_NATIVE))
        .debug_fallback()
}

fn build_parser() -> impl Parser<Command> {
    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file to compile");
    let output = short('o')
        .long("output")
        .help("Where to write artifacts (default: a.out)")
        .argument::<PathBuf>("PATH")
        .optional();
    let emit = long("emit")
        .help("Print an intermediate stage: barb or machine")
        .argument::<String>("STAGE")
        .parse(|stage| match stage.as_str() {
            "barb" => Ok(Emit::Barb),
            "machine" => Ok(Emit::Machine),
            _ => Err("expected barb or machine"),
        })
        .optional();
    construct!(Command::Build {
        output,
        emit,
        target,
        source,
    })
    .to_options()
    .descr("Compile a Faun program")
    .command("build")
}

fn cli() -> OptionParser<Command> {
    let target = selected_target().optional();
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    let check = construct!(Command::Check { target, source })
        .to_options()
        .descr("Load and check a Faun program")
        .command("check");

    let target = target_parser();
    let source = positional::<PathBuf>("PATH").help("The source file to compile and run");
    let run = construct!(Command::Run { target, source })
        .to_options()
        .descr("Compile a Faun program for the selected machine and run it")
        .command("run");

    choice([check.boxed(), build_parser().boxed(), run.boxed()])
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

fn dispatch(command: Command) -> Result<ExitCode, Box<dyn Error>> {
    match command {
        Command::Check { source, target } => {
            faun::check(&source, target.is_some())?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Build {
            source,
            output,
            emit,
            target,
        } => {
            build(&source, target, output, emit)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Run { source, target } => run(&source, target),
    }
}

fn build(
    source: &Path,
    target: &dyn Target,
    output: Option<PathBuf>,
    emit: Option<Emit>,
) -> Result<(), Box<dyn Error>> {
    if emit.is_some() && output.is_some() {
        return Err("--output cannot be used with --emit; redirect stdout instead".into());
    }
    match emit {
        Some(Emit::Barb) => {
            let mut program = faun::barb(source, target)?;
            faun_core::barb::optimize(&mut program);
            print!("{}", program.render());
        }
        Some(Emit::Machine) => print!("{}", faun::machine(source, target)?.render()),
        None => {
            let artifacts = target.compile(&faun::machine(source, target)?)?;
            let output = output.unwrap_or_else(|| PathBuf::from("a.out"));
            for artifact in write_artifacts(&output, artifacts)? {
                println!("wrote {}", artifact.path.display());
            }
        }
    }
    Ok(())
}

/// Compile for a target with a native executable, run it, and exit as it did.
fn run(source: &Path, target: &dyn Target) -> Result<ExitCode, Box<dyn Error>> {
    let artifacts = target.compile(&faun::machine(source, target)?)?;
    if !artifacts.iter().any(|artifact| artifact.executable) {
        return Err("the selected target did not emit a native executable".into());
    }
    let directory = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
    fs::create_dir_all(&directory)?;
    let artifacts = write_artifacts(&directory.join("program"), artifacts)?;
    let executable = artifacts
        .iter()
        .find(|artifact| artifact.executable)
        .expect("an executable artifact was checked before writing");
    let status = Process::new(&executable.path).status();
    fs::remove_dir_all(directory)?;
    let code = status?.code().unwrap_or(1);
    Ok(ExitCode::from(u8::try_from(code).unwrap_or(1)))
}

struct WrittenArtifact {
    path: PathBuf,
    executable: bool,
}

fn write_artifacts(
    output: &Path,
    artifacts: Vec<Artifact>,
) -> Result<Vec<WrittenArtifact>, Box<dyn Error>> {
    let mut written = Vec::with_capacity(artifacts.len());
    for artifact in artifacts {
        let mut path = output.to_path_buf().into_os_string();
        path.push(artifact.extension);
        let path = PathBuf::from(path);
        fs::write(&path, artifact.bytes)?;
        #[cfg(unix)]
        if artifact.executable {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755))?;
        }
        written.push(WrittenArtifact {
            path,
            executable: artifact.executable,
        });
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_emits_intermediate_stages_for_any_target() {
        let barb = cli()
            .run_inner(&[
                "build",
                "--target",
                "wasm32-wasi",
                "--emit",
                "barb",
                "example.fn",
            ])
            .unwrap();
        assert!(matches!(
            barb,
            Command::Build {
                target,
                source,
                emit: Some(Emit::Barb),
                output: None,
            } if target.name() == "wasm32-wasi" && source == Path::new("example.fn")
        ));

        let machine = cli()
            .run_inner(&[
                "build",
                "--target",
                "mos6502-sim65",
                "--emit",
                "machine",
                "example.fn",
            ])
            .unwrap();
        assert!(matches!(
            machine,
            Command::Build {
                emit: Some(Emit::Machine),
                ..
            }
        ));
    }

    #[test]
    fn build_rejects_unknown_emit_stages() {
        let error = cli()
            .run_inner(&["build", "--emit", "ir", "example.fn"])
            .unwrap_err()
            .unwrap_stderr();
        assert!(error.contains("expected barb or machine"), "{error}");
    }

    #[test]
    fn build_rejects_an_output_path_for_stdout_ir() {
        let command = cli()
            .run_inner(&[
                "build",
                "--target",
                "wasm32-wasi",
                "--emit",
                "barb",
                "--output",
                "program.barb",
                "example.fn",
            ])
            .unwrap();
        let error = dispatch(command).unwrap_err().to_string();
        assert!(error.contains("redirect stdout"), "{error}");
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
