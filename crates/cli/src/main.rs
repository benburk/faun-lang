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
    Check { source: PathBuf },
    Lower { source: PathBuf, entry: String },
}

fn cli() -> OptionParser<Command> {
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    let check = construct!(Command::Check { source })
        .to_options()
        .descr("Load and check a Faun program without compiling it")
        .command("check");

    let source = positional::<PathBuf>("PATH").help("The source file to lower");
    let entry = long("entry")
        .help("Parameterless value to use as the Barb entry")
        .argument::<String>("NAME");
    let lower = construct!(Command::Lower { entry, source })
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
        Command::Check { source } => check(&source),
        Command::Lower { source, entry } => lower(&source, &entry),
    }
}

fn check(source: &PathBuf) -> Result<(), String> {
    let prelude = std::env::var_os("ORI_STD").map(PathBuf::from);
    let loaded = faun_frontend::modules::load(std::slice::from_ref(source), prelude.as_deref())
        .map_err(|error| error.to_string())?;
    let blessed = loaded
        .prelude
        .map(|_| faun_frontend::blessed::PreludeIds::resolve(&loaded))
        .transpose()
        .map_err(|error| error.to_string())?;
    let resolved = faun_frontend::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    if let Some(blessed) = blessed {
        faun_frontend::check::program(&resolved, &blessed).map_err(|error| error.to_string())?;
    }
    Ok(())
}

fn lower(source: &PathBuf, entry: &str) -> Result<(), String> {
    let prelude = std::env::var_os("ORI_STD")
        .map(PathBuf::from)
        .ok_or_else(|| "lowering requires ORI_STD to name the standard package".to_string())?;
    let loaded =
        faun_frontend::modules::load(std::slice::from_ref(source), Some(prelude.as_path()))
            .map_err(|error| error.to_string())?;
    let blessed =
        faun_frontend::blessed::PreludeIds::resolve(&loaded).map_err(|error| error.to_string())?;
    let resolved = faun_frontend::resolve::resolve(loaded).map_err(|error| error.to_string())?;
    let checked =
        faun_frontend::check::program(&resolved, &blessed).map_err(|error| error.to_string())?;
    let program = faun_frontend::lower::named_program(&resolved, &checked, &blessed, entry)
        .map_err(|error| error.to_string())?;
    print!("{}", program.render());
    Ok(())
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
            Command::Check { source } if source == std::path::Path::new("example.fn")
        ));
    }

    #[test]
    fn lower_takes_an_entry_and_source_path() {
        let command = cli()
            .run_inner(&["lower", "--entry", "answer", "example.fn"][..])
            .unwrap();
        assert!(matches!(
            command,
            Command::Lower { source, entry }
                if source == std::path::Path::new("example.fn") && entry == "answer"
        ));
    }
}
