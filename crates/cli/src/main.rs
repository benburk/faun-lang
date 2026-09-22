use std::fs;
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
    let source = positional::<PathBuf>("PATH").help("The Ori-syntax source file to parse");
    construct!(Command::Check { source })
        .to_options()
        .descr("Parse a Faun program without compiling it")
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
            let text = fs::read_to_string(&source)
                .map_err(|error| format!("{}: {error}", source.display()))?;
            faun::surface::parse(&text).map_err(|error| format!("{}:{error}", source.display()))?;
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
