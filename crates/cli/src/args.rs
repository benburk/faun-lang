//! The `faun` command line: what each subcommand takes, parsed into a
//! [`Command`].

use std::path::PathBuf;

use bpaf::{Parser, choice, construct, long, positional, short};
use faun_core::targets::{Favour, SymbolTable, Target};

use crate::{NATIVE, TARGETS};

#[derive(Clone, Debug)]
pub(crate) enum Command {
    Check {
        target: &'static dyn Target,
        source: PathBuf,
    },
    Build {
        target: &'static dyn Target,
        source: PathBuf,
        output: PathBuf,
        favour: Favour,
        symbols: SymbolTable,
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
pub(crate) enum Stage {
    Barb,
    Machine,
    /// The target's own rendering of what it encodes.
    Target,
}

/// Parse this process's arguments, printing help or an error and exiting
/// where they ask for no command.
pub(crate) fn parse() -> Command {
    choice([
        check().boxed(),
        build().boxed(),
        run().boxed(),
        test().boxed(),
        emit().boxed(),
    ])
    .to_options()
    .descr("The Faun compiler")
    .version(env!("CARGO_PKG_VERSION"))
    .run()
}

fn check() -> impl Parser<Command> {
    let target = target();
    let source = positional::<PathBuf>("PATH").help("The source file to check");
    construct!(Command::Check { target, source })
        .to_options()
        .descr("Check a Faun program against the selected machine's host")
        .command("check")
}

fn build() -> impl Parser<Command> {
    let target = target();
    let source = positional::<PathBuf>("PATH").help("The source file to compile");
    let output = short('o')
        .long("output")
        .help("Where to write artifacts")
        .argument::<PathBuf>("PATH")
        .fallback(PathBuf::from("a.out"))
        .debug_fallback();
    let favour = long("small")
        .help("Favour a smaller program over a faster one")
        .switch()
        .map(|small| if small { Favour::Size } else { Favour::Speed });
    let symbols = long("symbols")
        .help("Name each function in the image and chain their frames, for a profiler or a disassembler")
        .switch()
        .map(|named| {
            if named {
                SymbolTable::Written
            } else {
                SymbolTable::Omitted
            }
        });
    construct!(Command::Build {
        output,
        symbols,
        target,
        favour,
        source,
    })
    .to_options()
    .descr("Compile a Faun program")
    .command("build")
}

fn run() -> impl Parser<Command> {
    let target = target();
    let source = positional::<PathBuf>("PATH").help("The source file to compile and run");
    let args = positional::<String>("ARGS")
        .help("What the program is run with; after `--`, even what looks like an option")
        .many();
    construct!(Command::Run {
        target,
        source,
        args
    })
    .to_options()
    .descr("Compile a Faun program for the selected machine and run it")
    .command("run")
}

fn test() -> impl Parser<Command> {
    let target = target();
    let source = positional::<PathBuf>("PATH").help("The source file whose package to test");
    construct!(Command::Test { target, source })
        .to_options()
        .descr("Run every `expect` in a Faun package on the selected machine")
        .command("test")
}

fn emit() -> impl Parser<Command> {
    let target = target();
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

/// `--target`, defaulting to [`NATIVE`] and required where there is none.
fn target() -> impl Parser<&'static dyn Target> {
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

const NO_NATIVE: &str = "no target runs on this machine, so --target is required";

fn unknown_target(name: &str) -> String {
    let known = TARGETS
        .iter()
        .map(|target| target.name())
        .collect::<Vec<_>>()
        .join(", ");
    format!("unknown target `{name}`, expected: {known}")
}
