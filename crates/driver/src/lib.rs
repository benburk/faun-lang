//! Reusable command driver for the primary Faun frontend.
//!
//! A compiler distribution supplies a static list of [`Backend`] values. The
//! driver owns command parsing and source-to-artifact orchestration; targets
//! remain small libraries depending only on `faun-core`. Commands load the
//! standard package supplied by the `faun` crate and require no environment
//! configuration.

use std::error::Error;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as Process, ExitCode};

use bpaf::{OptionParser, Parser, choice, construct, long, positional, short};
use faun_core::targets::{Artifact, Target};

/// A source host module paired with the machine target that implements it.
#[derive(Clone, Copy, Debug)]
enum HostModule {
    /// Resolve `hosts/<name>.fn` beside the selected standard package.
    Standard(&'static str),
    /// Load a host module shipped by an external target crate.
    Path(&'static str),
}

/// One backend offered by a compiler distribution.
#[derive(Clone, Copy)]
pub struct Backend {
    target: &'static dyn Target,
    host: HostModule,
    native: bool,
}

impl fmt::Debug for Backend {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.target.name())
    }
}

impl Backend {
    /// Register a target whose host module belongs to the standard package.
    #[must_use]
    pub const fn standard(target: &'static dyn Target, host: &'static str, native: bool) -> Self {
        Self {
            target,
            host: HostModule::Standard(host),
            native,
        }
    }

    /// Register an external target and the host module it ships.
    #[must_use]
    pub const fn external(target: &'static dyn Target, host: &'static str, native: bool) -> Self {
        Self {
            target,
            host: HostModule::Path(host),
            native,
        }
    }

    fn host_path(self, prelude: &Path) -> Result<PathBuf, String> {
        match self.host {
            HostModule::Standard(name) => {
                let directory = prelude
                    .parent()
                    .ok_or_else(|| "the standard package path has no parent".to_string())?;
                Ok(directory.join("hosts").join(format!("{name}.fn")))
            }
            HostModule::Path(path) => Ok(PathBuf::from(path)),
        }
    }
}

#[derive(Clone, Debug)]
enum Command {
    Check {
        target: Option<&'static Backend>,
        source: PathBuf,
    },
    Build {
        target: &'static Backend,
        source: PathBuf,
        output: Option<PathBuf>,
        emit: Option<Emit>,
    },
    Run {
        target: &'static Backend,
        source: PathBuf,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Emit {
    Barb,
    Machine,
}

fn selected_target(backends: &'static [Backend]) -> impl Parser<&'static Backend> {
    long("target")
        .help("Machine to compile for")
        .argument::<String>("TARGET")
        .parse(move |name| {
            backends
                .iter()
                .find(|backend| backend.target.name() == name)
                .ok_or_else(|| unknown_target(backends, &name))
        })
}

fn target_parser(backends: &'static [Backend]) -> impl Parser<&'static Backend> {
    selected_target(backends)
        .fallback_with(move || {
            backends
                .iter()
                .find(|backend| backend.native)
                .ok_or(NO_NATIVE)
        })
        .debug_fallback()
}

fn build_parser(backends: &'static [Backend]) -> impl Parser<Command> {
    let target = target_parser(backends);
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

fn cli(backends: &'static [Backend]) -> OptionParser<Command> {
    let target = selected_target(backends).optional();
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    let check = construct!(Command::Check { target, source })
        .to_options()
        .descr("Load and check a Faun program")
        .command("check");

    let target = target_parser(backends);
    let source = positional::<PathBuf>("PATH").help("The source file to compile and run");
    let run = construct!(Command::Run { target, source })
        .to_options()
        .descr("Compile a Faun program for the selected machine and run it")
        .command("run");

    choice([check.boxed(), build_parser(backends).boxed(), run.boxed()])
        .to_options()
        .descr("The Faun compiler")
        .version(env!("CARGO_PKG_VERSION"))
}

const NO_NATIVE: &str = "no backend for this machine, so --target is required";

fn unknown_target(backends: &[Backend], name: &str) -> String {
    let known = backends
        .iter()
        .map(|backend| backend.target.name())
        .collect::<Vec<_>>()
        .join(", ");
    format!("unknown target `{name}`, expected: {known}")
}

fn validate_backends(backends: &[Backend]) -> Result<(), String> {
    if backends.is_empty() {
        return Err("a compiler distribution must register a backend".to_string());
    }
    if backends.iter().filter(|backend| backend.native).count() > 1 {
        return Err("a compiler distribution may register only one native backend".to_string());
    }
    for (index, backend) in backends.iter().enumerate() {
        let name = backend.target.name();
        if name.is_empty() {
            return Err("a registered backend has an empty name".to_string());
        }
        if backends[..index]
            .iter()
            .any(|earlier| earlier.target.name() == name)
        {
            return Err(format!("more than one backend is named `{name}`"));
        }
    }
    Ok(())
}

/// Run the standard command interface against exactly the supplied backends.
///
/// A custom target executable normally does nothing except construct one
/// [`Backend`] and call this function.
#[must_use]
pub fn run(backends: &'static [Backend]) -> ExitCode {
    if let Err(error) = validate_backends(backends) {
        eprintln!("faun: {error}");
        return ExitCode::FAILURE;
    }
    match dispatch(cli(backends).run()) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("faun: {error}");
            ExitCode::FAILURE
        }
    }
}

fn dispatch(command: Command) -> Result<ExitCode, Box<dyn Error>> {
    match command {
        Command::Check { source, target } => {
            check(&source, target.copied())?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Build {
            source,
            output,
            emit,
            target,
        } => {
            build(&source, *target, output, emit)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Run { source, target } => {
            let artifacts = compile(&source, *target)?;
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
    }
}

fn build(
    source: &Path,
    backend: Backend,
    output: Option<PathBuf>,
    emit: Option<Emit>,
) -> Result<(), Box<dyn Error>> {
    if emit.is_some() && output.is_some() {
        return Err("--output cannot be used with --emit; redirect stdout instead".into());
    }
    match emit {
        Some(Emit::Barb) => print!("{}", optimized_application(source, backend)?.render()),
        Some(Emit::Machine) => print!("{}", machine(source, backend)?.render()),
        None => {
            let artifacts = compile(source, backend)?;
            let output = output.unwrap_or_else(|| PathBuf::from("a.out"));
            for artifact in write_artifacts(&output, artifacts)? {
                println!("wrote {}", artifact.path.display());
            }
        }
    }
    Ok(())
}

fn check(source: &Path, backend: Option<Backend>) -> Result<(), String> {
    let prelude = faun::standard_path();
    let host = backend
        .map(|backend| backend.host_path(prelude))
        .transpose()?;
    let loaded =
        faun::modules::load_with_host(&[source.to_path_buf()], Some(prelude), host.as_deref())
            .map_err(|error| error.to_string())?;
    let blessed = faun::blessed::PreludeIds::resolve(&loaded).map_err(|error| error.to_string())?;
    let host_ids = backend
        .map(|_| faun::host::HostIds::resolve(&loaded, &blessed))
        .transpose()
        .map_err(|error| error.to_string())?;
    let resolved = faun::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    let checked = faun::check::program(&resolved, &blessed).map_err(|error| error.to_string())?;
    if let Some(host) = host_ids {
        faun::check::application(&resolved, &checked, &host).map_err(|error| error.to_string())?;
    }
    Ok(())
}

fn lower_application(source: &Path, backend: Backend) -> Result<faun_core::barb::Program, String> {
    let prelude = faun::standard_path();
    let host = backend.host_path(prelude)?;
    let loaded = faun::modules::load_with_host(&[source.to_path_buf()], Some(prelude), Some(&host))
        .map_err(|error| error.to_string())?;
    let blessed = faun::blessed::PreludeIds::resolve(&loaded).map_err(|error| error.to_string())?;
    let host =
        faun::host::HostIds::resolve(&loaded, &blessed).map_err(|error| error.to_string())?;
    let resolved = faun::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    let checked = faun::check::program(&resolved, &blessed).map_err(|error| error.to_string())?;
    faun::lower::application(
        &resolved,
        &checked,
        &blessed,
        &host,
        &backend.target.routines(),
    )
    .map_err(|error| error.to_string())
}

fn optimized_application(
    source: &Path,
    backend: Backend,
) -> Result<faun_core::barb::Program, String> {
    let mut program = lower_application(source, backend)?;
    faun_core::barb::optimize(&mut program);
    Ok(program)
}

fn machine(source: &Path, backend: Backend) -> Result<faun_core::ir::Program, String> {
    let mut program = optimized_application(source, backend)?;
    faun_core::machine(&mut program, &backend.target.routines())
}

fn compile(source: &Path, backend: Backend) -> Result<Vec<Artifact>, String> {
    backend.target.compile(&machine(source, backend)?)
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

    #[derive(Debug)]
    struct TestTarget;

    impl Target for TestTarget {
        fn name(&self) -> &'static str {
            "test-target"
        }

        fn word(&self) -> u16 {
            32
        }

        fn provides(&self) -> &'static [&'static str] {
            &[]
        }

        fn emit(&self, _: &faun_core::ir::Program) -> Vec<Artifact> {
            Vec::new()
        }
    }

    const TEST_TARGET: TestTarget = TestTarget;
    const BACKENDS: [Backend; 1] = [Backend::standard(&TEST_TARGET, "test-target", true)];

    #[test]
    fn build_emits_intermediate_stages_for_registered_targets() {
        let barb = cli(&BACKENDS)
            .run_inner(&[
                "build",
                "--target",
                "test-target",
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
            } if target.target.name() == "test-target" && source == Path::new("example.fn")
        ));

        let machine = cli(&BACKENDS)
            .run_inner(&["build", "--emit", "machine", "example.fn"])
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
        let error = cli(&BACKENDS)
            .run_inner(&["build", "--emit", "ir", "example.fn"])
            .unwrap_err()
            .unwrap_stderr();
        assert!(error.contains("expected barb or machine"), "{error}");
    }

    #[test]
    fn build_rejects_an_output_path_for_stdout_ir() {
        let command = cli(&BACKENDS)
            .run_inner(&[
                "build",
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
    fn native_target_is_the_default_and_unknown_targets_name_the_registry() {
        let parsed = cli(&BACKENDS).run_inner(&["build", "example.fn"]).unwrap();
        assert!(matches!(parsed, Command::Build { target, .. } if target.native));
        let error = cli(&BACKENDS)
            .run_inner(&["build", "--target", "other", "example.fn"])
            .unwrap_err()
            .unwrap_stderr();
        assert!(error.contains("test-target"), "{error}");
    }

    #[test]
    fn backend_registration_rejects_empty_duplicate_and_multiple_native_sets() {
        assert!(validate_backends(&[]).is_err());
        let duplicate = Backend::standard(&TEST_TARGET, "test-target", false);
        assert!(validate_backends(&[duplicate, duplicate]).is_err());
        let second = Backend::external(&TEST_TARGET, "host.fn", true);
        assert!(validate_backends(&[BACKENDS[0], second]).is_err());
    }
}
