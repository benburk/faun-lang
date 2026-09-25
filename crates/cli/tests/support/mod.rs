//! A Faun package in its own directory, lowered for x86-64 and run on the
//! reference interpreter, which checks the tiers above a target whatever
//! any one backend can yet hold.

// Each test crate that includes this uses the part it needs.
#![allow(dead_code)]

use std::fs;
use std::path::PathBuf;

use faun_core::ir::evaluate::{self, Error, Host, HostResult, Memory};
use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;
use num_bigint::BigUint;

/// A module every package may import, whose constructors it keeps.
pub(crate) const SEALED: &str = "exports {Failure accept Sized}

Failure : [NotFound SomethingElse]

Sized(a) = where
  a.size : a -> Nat

accept : Failure -> Nat
accept(NotFound) -> 1
accept(SomethingElse) -> 2
";

/// A package whose entry imports the host and holds `source`, written
/// indented as a Rust string continues; removed when dropped.
pub(crate) struct Package(PathBuf);

impl Package {
    pub(crate) fn new(name: &str, source: &str) -> Self {
        let directory = std::env::temp_dir().join(format!(
            "faun-{}-{}",
            name.replace(|c: char| !c.is_ascii_alphanumeric(), "-"),
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        // The first line starts after the quote; the rest are indented as
        // the Rust source around them, by as much as the least of them.
        let indent = source
            .lines()
            .skip(1)
            .filter(|line| !line.trim().is_empty())
            .map(|line| line.len() - line.trim_start().len())
            .min()
            .unwrap_or(0);
        let body = source
            .lines()
            .enumerate()
            .map(|(at, line)| {
                if at == 0 {
                    line
                } else {
                    line.get(indent..).unwrap_or("")
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        fs::write(
            directory.join("main.fn"),
            format!("import std.host {{Host}}\n\n{body}\n"),
        )
        .unwrap();
        fs::write(directory.join("sealed.fn"), SEALED).unwrap();
        Self(directory)
    }

    pub(crate) fn entry(&self) -> PathBuf {
        self.0.join("main.fn")
    }

    /// Why checking or lowering refuses the package.
    pub(crate) fn refusal(&self) -> String {
        faun::lower_to_barb(&self.entry(), &X86_64Linux).map_or_else(
            |error| error.message,
            |_| "nothing: the package was accepted".to_owned(),
        )
    }

    /// The status the program exits with, handed an `argc` of one.
    pub(crate) fn run(&self) -> u32 {
        run_file(&self.entry(), &[]).0
    }
}

/// Run the program at `entry` on the reference interpreter, handed an
/// `argc` of one and `input` on standard input: the status it exits with,
/// and what it wrote to standard output.
pub(crate) fn run_file(entry: &std::path::Path, input: &[u8]) -> (u32, String) {
    run_failing(entry, input, None)
}

/// The same, where every write to standard output fails with `errno`, as
/// a kernel says so: that far short of the top of a word.
pub(crate) fn run_failing(
    entry: &std::path::Path,
    input: &[u8],
    errno: Option<u64>,
) -> (u32, String) {
    let barb = faun::lower_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    run_barb(barb, input, errno)
}

/// Build the package at `entry` as `faun test` does and run it: the lines,
/// `path:line`, of the expectations that do not hold, and how many there are.
pub(crate) fn test_file(entry: &std::path::Path) -> (Vec<String>, usize) {
    let tests = faun::lower_tests_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    let count = tests.expectations.len();
    let (status, written) = run_barb(tests.barb, &[], None);
    assert_eq!(status, 0, "{written}");
    let failed = written
        .split_whitespace()
        .map(|number| {
            let location = &tests.expectations[number.parse::<usize>().unwrap() - 1];
            format!(
                "{}:{}",
                location.path.file_name().unwrap().to_string_lossy(),
                location.line
            )
        })
        .collect();
    (failed, count)
}

/// As [`test_file`], with every definition claimed to compute a float
/// answering by its body rather than by the host's instruction: the
/// standard's own arithmetic, asked the same questions.
pub(crate) fn test_file_by_definitions(entry: &std::path::Path) -> (Vec<String>, usize) {
    let mut tests = faun::lower_tests_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    tests.barb.disclaim();
    let count = tests.expectations.len();
    // Software arithmetic takes the interpreter many steps an operation.
    let (status, written) = run_barb_fueled(tests.barb, &[], None, 20_000_000_000);
    assert_eq!(status, 0, "{written}");
    let failed = written
        .split_whitespace()
        .map(|number| {
            let location = &tests.expectations[number.parse::<usize>().unwrap() - 1];
            format!(
                "{}:{}",
                location.path.file_name().unwrap().to_string_lossy(),
                location.line
            )
        })
        .collect();
    (failed, count)
}

fn run_barb(barb: faun_core::barb::Program, input: &[u8], errno: Option<u64>) -> (u32, String) {
    run_barb_fueled(barb, input, errno, 100_000_000)
}

fn run_barb_fueled(
    mut barb: faun_core::barb::Program,
    input: &[u8],
    errno: Option<u64>,
    fuel: u64,
) -> (u32, String) {
    faun_core::barb::optimize(&mut barb);
    let machine = faun_core::lower_to_machine_ir(&mut barb, &X86_64Linux.routines())
        .unwrap_or_else(|error| panic!("{error}"));
    let prepared = X86_64Linux
        .prepare(&machine)
        .unwrap_or_else(|error| panic!("{error}"));
    let main = prepared.entry();
    // `argc` is handed only where the program reads it.
    let handed = vec![BigUint::from(1u8); prepared.parameter_names(main).count()];
    let mut streams = Streams {
        input: input.iter().copied().collect(),
        output: Vec::new(),
        errno,
    };
    let evaluation = evaluate::evaluate(
        &prepared,
        main,
        &handed,
        evaluate::Config {
            fuel,
            ..evaluate::Config::default()
        },
        &mut streams,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let halted = evaluation.halted().expect("a program that exits");
    let status = u32::try_from(&halted[0]).expect("a status");
    (
        status,
        String::from_utf8(streams.output).expect("text written"),
    )
}

impl Drop for Package {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A host with standard input to hand out, standard output to keep, and
/// standard error to drop.
struct Streams {
    input: std::collections::VecDeque<u8>,
    output: Vec<u8>,
    /// What every write to standard output fails with, if it fails.
    errno: Option<u64>,
}

impl Host for Streams {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        let word = |value: &BigUint| u64::try_from(value).expect("a word");
        match name {
            "exit!" => Ok(HostResult::Halt(args.to_vec())),
            // Up to as many as asked, where they are to lie: how many.
            "take_in!" => {
                let asked = usize::try_from(word(&args[1])).expect("a count");
                let taken: Vec<u8> = (0..asked).map_while(|_| self.input.pop_front()).collect();
                memory.write(word(&args[0]), &taken)?;
                Ok(HostResult::Return(vec![BigUint::from(taken.len())]))
            }
            // All of it, every time: how many.
            "put_out!" if self.errno.is_some() => {
                let errno = self.errno.expect("a failing write");
                Ok(HostResult::Return(vec![BigUint::from(
                    0u64.wrapping_sub(errno),
                )]))
            }
            "put_out!" | "put_err!" => {
                let len = usize::try_from(word(&args[1])).expect("a length");
                if name == "put_out!" {
                    self.output
                        .extend_from_slice(memory.read(word(&args[0]), len)?);
                }
                Ok(HostResult::Return(vec![BigUint::from(len)]))
            }
            _ => Err(Error::Host(name.to_owned())),
        }
    }
}
