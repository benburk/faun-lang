use std::path::PathBuf;
use std::process::ExitCode;

use bpaf::OptionParser;
use bpaf::Parser;
use bpaf::construct;
use bpaf::positional;

// Parsing constructs many short-lived AST vectors and boxes. Keeping the
// allocator optimized in development builds matters as much as optimizing the
// parser itself; the system allocator made the mixed benchmark about 20% slower.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[derive(Clone, Debug)]
enum Command {
    Check { source: PathBuf },
}

fn cli() -> OptionParser<Command> {
    let source = positional::<PathBuf>("PATH").help("The Ori-syntax source file to check");
    construct!(Command::Check { source })
        .to_options()
        .descr("Load and check a Faun program without compiling it")
        .command("check")
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
        Command::Check { source } => {
            let prelude = std::env::var_os("ORI_STD").map(PathBuf::from);
            let loaded =
                faun::surface::modules::load(std::slice::from_ref(&source), prelude.as_deref())
                    .map_err(|error| error.to_string())?;
            let blessed = loaded
                .prelude
                .map(|_| faun::surface::blessed::PreludeIds::resolve(&loaded))
                .transpose()
                .map_err(|error| error.to_string())?;
            let resolved =
                faun::surface::resolve::resolve(loaded).map_err(|error| error.to_string())?;
            if let Some(blessed) = blessed {
                faun::surface::check::program(&resolved, &blessed)
                    .map_err(|error| error.to_string())?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_takes_an_ori_source_path() {
        cli().check_invariants(false);
        let command = cli().run_inner(&["check", "example.ori"][..]).unwrap();
        let Command::Check { source } = command;
        assert_eq!(source, PathBuf::from("example.ori"));
    }
}
