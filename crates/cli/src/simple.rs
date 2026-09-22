use std::error::Error;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::process::ExitCode;

use bpaf::OptionParser;
use bpaf::Parser;
use bpaf::choice;
use bpaf::construct;
use bpaf::long;
use bpaf::positional;
use bpaf::short;

use faun::targets::Target;
use faun_aarch64_macos::Aarch64Macos;
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(test)]
mod tests;

/// Every target this was built with, in the order they were written.
///
/// Nothing else names all four. A compiler for four machines has to hold
/// four backends, and this is the thing that has to: what a target is, and
/// how to reach one, are questions every other crate answers for itself.
const ALL: [&dyn Target; 4] = [&X86_64Linux, &Wasm32Wasi, &Mos6502Sim65, &Aarch64Macos];

/// The one native to the machine this is running on, if there is one here
/// for it. `None` means `--target` is not optional here.
const HOST: Option<&dyn Target> = if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
    Some(&X86_64Linux)
} else if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
    Some(&Aarch64Macos)
} else {
    None
};

#[derive(Clone, Debug)]
enum Command {
    Build {
        source: PathBuf,
        output: PathBuf,
        target: &'static dyn Target,
    },
    Run {
        source: PathBuf,
    },
    Inspect {
        source: PathBuf,
        target: &'static dyn Target,
        stage: Stage,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stage {
    Barb,
    Ir,
    PreparedIr,
}

fn target() -> impl Parser<&'static dyn Target> {
    long("target")
        .help("Machine to compile for")
        .argument::<String>("TARGET")
        .parse(|name| {
            ALL.into_iter()
                .find(|target| target.name() == name)
                .ok_or_else(|| unknown(&name))
        })
        .fallback_with(|| HOST.ok_or(NO_HOST))
        .debug_fallback()
}

fn inspection() -> impl Parser<Command> {
    let source = positional::<PathBuf>("PATH").help("The program to inspect");
    let stage = long("emit")
        .help("Inspection stage: barb (optimized), ir (lowered), prepared-ir (target-ready)")
        .argument::<String>("STAGE")
        .parse(|stage| match stage.as_str() {
            "barb" => Ok(Stage::Barb),
            "ir" => Ok(Stage::Ir),
            "prepared-ir" => Ok(Stage::PreparedIr),
            _ => Err("expected barb, ir or prepared-ir"),
        });
    construct!(Command::Inspect { target(), stage, source })
        .to_options()
        .descr("Print an intermediate representation to stdout")
        .command("inspect")
}

fn cli() -> OptionParser<Command> {
    let source = || positional::<PathBuf>("PATH").help("The program to compile");

    let output = short('o')
        .long("output")
        .help("Where to write the result")
        .argument::<PathBuf>("PATH")
        .fallback(PathBuf::from("a.out"))
        .debug_fallback();

    let build = construct!(Command::Build {
        output,
        target(),
        source(),
    })
    .to_options()
    .descr("Compile the program to an executable")
    .command("build");

    let run = construct!(Command::Run { source() })
        .to_options()
        .descr("Compile the program for this machine and run it")
        .command("run");

    choice([build.boxed(), run.boxed(), inspection().boxed()])
        .to_options()
        .descr("The archived simple Faun frontend")
        .version(env!("CARGO_PKG_VERSION"))
}

const NO_HOST: &str = "no backend for this machine, so --target is required";

fn unknown(name: &str) -> String {
    let known: Vec<_> = ALL.iter().map(|target| target.name()).collect();
    let known = known.join(", ");
    format!("unknown target `{name}`, expected: {known}")
}

fn main() -> ExitCode {
    match dispatch(cli().run()) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("faun-simple: {error}");
            ExitCode::FAILURE
        }
    }
}

fn dispatch(command: Command) -> Result<ExitCode, Box<dyn Error>> {
    match command {
        Command::Inspect {
            source,
            target,
            stage,
        } => {
            let text = fs::read_to_string(&source)?;
            let rendered = inspect(&text, target, stage)
                .map_err(|error| format!("{}: {error}", source.display()))?;
            print!("{rendered}");
            Ok(ExitCode::SUCCESS)
        }
        Command::Build {
            source,
            output,
            target,
        } => {
            let program = read(&source, target)?;
            for path in write(target, &output, &program)? {
                println!("wrote {}", path.display());
            }
            Ok(ExitCode::SUCCESS)
        }
        Command::Run { source } => {
            let target = HOST.ok_or(NO_HOST)?;
            let program = read(&source, target)?;
            let dir = std::env::temp_dir().join(format!("faun-run-{}", std::process::id()));
            fs::create_dir_all(&dir)?;

            let status = write(target, &dir.join("program"), &program)?
                .first()
                .map(Process::new)
                .expect("a target emits at least one file")
                .status();
            fs::remove_dir_all(&dir)?;

            let code = status?.code().unwrap_or(1);
            Ok(ExitCode::from(u8::try_from(code).unwrap_or(1)))
        }
    }
}

/// Stop at the requested tier; Barb inspection does not require a runtime
/// representation, machine IR has been through its own passes, and prepared
/// IR establishes target acceptance as well.
fn inspect(text: &str, target: &dyn Target, stage: Stage) -> Result<String, String> {
    let routines = target.routines();
    match stage {
        Stage::Barb => Ok(faun_simple::read_barb_with_options(
            text,
            &routines,
            &faun::barb::OptimizeOptions::default(),
        )?
        .render()),
        Stage::Ir => {
            let program = faun_simple::read(text, &routines)?;
            faun::ir::validate(&program)?;
            Ok(program.render())
        }
        Stage::PreparedIr => {
            let program = faun_simple::read(text, &routines)?;
            Ok(target.prepare(&program)?.render())
        }
    }
}

/// The program at `path`, read and lowered.
fn read(path: &Path, target: &dyn Target) -> Result<faun::ir::Program, Box<dyn Error>> {
    let text = fs::read_to_string(path)?;
    faun_simple::read(&text, &target.routines())
        .map_err(|error| format!("{}: {error}", path.display()).into())
}

fn write(
    target: &'static dyn Target,
    output: &Path,
    program: &faun::ir::Program,
) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let artifacts = target.compile(program)?;
    let mut written = Vec::new();

    for artifact in artifacts {
        let mut path = output.to_path_buf().into_os_string();
        path.push(artifact.extension);
        let path = PathBuf::from(path);

        fs::write(&path, &artifact.bytes)?;

        #[cfg(unix)]
        if artifact.executable {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755))?;
        }

        written.push(path);
    }

    Ok(written)
}
