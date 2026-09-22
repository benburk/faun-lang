use std::path::PathBuf;
use std::process::ExitCode;

use bpaf::OptionParser;
use bpaf::Parser;
use bpaf::choice;
use bpaf::construct;
use bpaf::long;
use bpaf::positional;

// Parsing constructs many short-lived AST vectors and boxes. Keeping the
// allocator optimized in development builds matters as much as optimizing the
// parser itself; the system allocator made the mixed benchmark about 20% slower.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[derive(Clone, Debug)]
enum Command {
    Check {
        host: Option<String>,
        source: PathBuf,
    },
    Lower {
        host: String,
        source: PathBuf,
    },
}

fn cli() -> OptionParser<Command> {
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    let host = long("host")
        .help("Host interface mounted at std.host")
        .argument::<String>("HOST")
        .optional();
    let check = construct!(Command::Check { host, source })
        .to_options()
        .descr("Load and check a Faun program without compiling it")
        .command("check");

    let source = positional::<PathBuf>("PATH").help("The source file to lower");
    let host = long("host")
        .help("Host interface mounted at std.host")
        .argument::<String>("HOST");
    let lower = construct!(Command::Lower { host, source })
        .to_options()
        .descr("Specialize a checked program and print Barb")
        .command("lower");

    choice([check.boxed(), lower.boxed()])
        .to_options()
        .descr("The Faun compiler")
        .version(env!("CARGO_PKG_VERSION"))
}

fn main() -> ExitCode {
    match dispatch(cli().run()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("faun: {error}");
            ExitCode::FAILURE
        }
    }
}

fn dispatch(command: Command) -> Result<(), String> {
    match command {
        Command::Check { source, host } => check(&source, host.as_deref()),
        Command::Lower { source, host } => lower(&source, &host),
    }
}

fn check(source: &PathBuf, host: Option<&str>) -> Result<(), String> {
    let prelude = std::env::var_os("ORI_STD").map(PathBuf::from);
    let host_path = host
        .map(|host| selected_host(prelude.as_deref(), host))
        .transpose()?;
    let loaded = faun_frontend::modules::load_with_host(
        std::slice::from_ref(source),
        prelude.as_deref(),
        host_path.as_deref(),
    )
    .map_err(|error| error.to_string())?;
    let blessed = loaded
        .prelude
        .map(|_| faun_frontend::blessed::PreludeIds::resolve(&loaded))
        .transpose()
        .map_err(|error| error.to_string())?;
    let host_ids = match (&blessed, host) {
        (Some(blessed), Some(_)) => Some(
            faun_frontend::host::HostIds::resolve(&loaded, blessed)
                .map_err(|error| error.to_string())?,
        ),
        _ => None,
    };
    let resolved = faun_frontend::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    if let Some(blessed) = blessed {
        let checked = faun_frontend::check::program(&resolved, &blessed)
            .map_err(|error| error.to_string())?;
        if let Some(host) = host_ids {
            faun_frontend::check::application(&resolved, &checked, &host)
                .map_err(|error| error.to_string())?;
        }
    }
    Ok(())
}

fn lower(source: &PathBuf, host: &str) -> Result<(), String> {
    let prelude = std::env::var_os("ORI_STD")
        .map(PathBuf::from)
        .ok_or_else(|| "lowering requires ORI_STD to name the standard package".to_string())?;
    let host_path = selected_host(Some(&prelude), host)?;
    let loaded = faun_frontend::modules::load_with_host(
        std::slice::from_ref(source),
        Some(prelude.as_path()),
        Some(host_path.as_path()),
    )
    .map_err(|error| error.to_string())?;
    let blessed =
        faun_frontend::blessed::PreludeIds::resolve(&loaded).map_err(|error| error.to_string())?;
    let host_ids = faun_frontend::host::HostIds::resolve(&loaded, &blessed)
        .map_err(|error| error.to_string())?;
    let resolved = faun_frontend::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    let checked =
        faun_frontend::check::program(&resolved, &blessed).map_err(|error| error.to_string())?;
    let routines = faun::platform::Routines::builtin().with_word(host_word_bits(host)?);
    let program =
        faun_frontend::lower::application(&resolved, &checked, &blessed, &host_ids, &routines)
            .map_err(|error| error.to_string())?;
    print!("{}", program.render());
    Ok(())
}

fn host_word_bits(host: &str) -> Result<u16, String> {
    match host {
        "x86-64-linux" | "aarch64-macos" => Ok(64),
        "wasm32-wasi" => Ok(32),
        "mos6502-sim65" => Ok(16),
        _ => Err(format!("unknown host `{host}`")),
    }
}

fn selected_host(prelude: Option<&std::path::Path>, host: &str) -> Result<PathBuf, String> {
    if host.is_empty()
        || !host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
    {
        return Err(format!("invalid host name `{host}`"));
    }
    let prelude = prelude.ok_or_else(|| {
        "a host interface requires ORI_STD to name the standard package".to_string()
    })?;
    let directory = prelude
        .parent()
        .ok_or_else(|| "ORI_STD has no package directory".to_string())?;
    Ok(directory.join("hosts").join(format!("{host}.fn")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_takes_a_source_path() {
        cli().check_invariants(false);
        let command = cli().run_inner(&["check", "example.fn"][..]).unwrap();
        assert!(matches!(
            command,
            Command::Check { source, host: None }
                if source == std::path::Path::new("example.fn")
        ));
    }

    #[test]
    fn lower_takes_a_host_and_source_path() {
        let command = cli()
            .run_inner(&["lower", "--host", "x86-64-linux", "example.fn"][..])
            .unwrap();
        assert!(matches!(
            command,
            Command::Lower { source, host }
                if source == std::path::Path::new("example.fn")
                    && host == "x86-64-linux"
        ));
    }
}
