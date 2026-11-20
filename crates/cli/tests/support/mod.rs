//! A Faun package in its own directory, lowered for x86-64 and run on the
//! reference interpreter, which checks the tiers above a target whatever
//! any one backend can yet hold.

// Each test crate that includes this uses the part it needs.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use faun_core::ir::evaluate::{self, Error, Host, HostResult, Memory};
use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;
use num_bigint::BigUint;

/// A module every package may import, whose constructors it keeps.
pub(crate) const SEALED: &str = "export {Failure, accept, Sized}

Failure : [NotFound, SomethingElse]

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
        // Numbered, since tests run side by side in one process, as
        // `cargo test` runs them, may each write a package of one name, and
        // the first done would remove the other's.
        static MADE: AtomicUsize = AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "faun-{}-{}-{}",
            name.replace(|c: char| !c.is_ascii_alphanumeric(), "-"),
            std::process::id(),
            MADE.fetch_add(1, Ordering::Relaxed)
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
    let barb = faun_frontend::lower_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    run_barb(barb, input, errno)
}

/// As [`run_file`], answering also the fuel the interpreter spent: a count
/// of the work the program did, the same from run to run.
pub(crate) fn run_counted(entry: &std::path::Path, input: &[u8]) -> (u32, String, u64) {
    let mut barb = faun_frontend::lower_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    let mut streams = Streams {
        input: input.iter().copied().collect(),
        ..Streams::default()
    };
    let (status, spent) = run_spending(&mut barb, &mut streams, 100_000_000);
    (
        status,
        String::from_utf8(streams.output).expect("text written"),
        spent,
    )
}

/// Files by name, beneath where a program runs.
pub(crate) type Directory = BTreeMap<String, Vec<u8>>;

/// The same, run where `files` lie: the status, what it wrote to standard
/// output, and the files as it left them.
pub(crate) fn run_among(entry: &std::path::Path, files: Directory) -> (u32, String, Directory) {
    let mut barb = faun_frontend::lower_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    let mut streams = Streams {
        files,
        ..Streams::default()
    };
    let status = run_on(&mut barb, &mut streams, 100_000_000);
    (
        status,
        String::from_utf8(streams.output).expect("text written"),
        streams.files,
    )
}

/// What a program did with the files it opened.
pub(crate) struct Handled {
    /// How many it left open when it ended.
    pub(crate) left_open: usize,
    /// How many times it read, wrote or closed one it had closed.
    pub(crate) misused: usize,
}

/// Run the program at `entry` as [`run_among`] does, among no files: the
/// status it exits with, and what it did with the files it opened.
pub(crate) fn run_handling(entry: &std::path::Path) -> (u32, Handled) {
    let mut barb = faun_frontend::lower_to_barb(entry, &X86_64Linux)
        .unwrap_or_else(|error| panic!("{}", error.message));
    let mut streams = Streams::default();
    let status = run_on(&mut barb, &mut streams, 100_000_000);
    let handled = Handled {
        left_open: streams.open.iter().flatten().count(),
        misused: streams.misused,
    };
    (status, handled)
}

/// The steps of the reference interpreter a file's expectations share.
const EXPECTATION_FUEL: u64 = 100_000_000;

/// Build the package at `entry` as `faun test` does and run it: the lines,
/// `path:line`, of the expectations that do not hold, and how many there are.
/// What each comparison among them saw is written to standard error, which
/// a failing test shows.
pub(crate) fn test_file(entry: &std::path::Path) -> (Vec<String>, usize) {
    told(entry, false, EXPECTATION_FUEL)
}

/// As [`test_file`], with every float operation answering by its body
/// rather than by the host's instruction: the standard's own arithmetic,
/// asked the same questions.
pub(crate) fn test_file_by_definitions(entry: &std::path::Path) -> (Vec<String>, usize) {
    // Software arithmetic takes the interpreter many steps an operation.
    told(entry, true, 20_000_000_000)
}

/// Each expectation that does not hold, as [`test_file`] tells it: where
/// it was written, and what a comparison saw.
fn told(entry: &std::path::Path, by_definitions: bool, fuel: u64) -> (Vec<String>, usize) {
    let (failed, count) =
        ask(entry, by_definitions, fuel).unwrap_or_else(|error| panic!("{error}"));
    for (_, said) in &failed {
        eprintln!("{said}");
    }
    (failed.into_iter().map(|(at, _)| at).collect(), count)
}

/// As [`test_file`], given `fuel` steps of the reference interpreter for
/// all of them: what each expectation that does not hold says, where it
/// was written and what a comparison saw, and how many there are; or, where
/// they run out of steps, which one did.
pub(crate) fn test_file_within(
    entry: &std::path::Path,
    fuel: u64,
) -> Result<(Vec<String>, usize), String> {
    let (failed, count) = ask(entry, false, fuel)?;
    Ok((failed.into_iter().map(|(_, said)| said).collect(), count))
}

/// `path:line` of where an expectation was written.
fn written(location: &faun_frontend::diagnostic::Location) -> String {
    format!(
        "{}:{}",
        location.path.file_name().unwrap().to_string_lossy(),
        location.line
    )
}

/// Ask the expectations of the package at `entry` on the reference
/// interpreter, given `fuel` steps among them; `by_definitions` takes
/// every float operation by its body. Each that does not hold, where it
/// was written and what it says, and how many there are; or, where they do
/// not finish within `fuel`, which expectation ran out and what those
/// before it took.
fn ask(
    entry: &std::path::Path,
    by_definitions: bool,
    fuel: u64,
) -> Result<(Vec<(String, String)>, usize), String> {
    let mut tests = faun_frontend::lower_tests_to_barb_using(
        entry,
        &X86_64Linux,
        &faun_frontend::packages::Packages::default(),
        faun_frontend::Reporting::Each,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    if by_definitions {
        tests.barb.walk_floats();
    }
    let count = tests.expectations.len();
    let mut barb = std::mem::take(&mut tests.barb);
    let mut streams = Streams::default();
    let ran = try_run_on(&mut barb, &mut streams, fuel);
    let answered = tests.answered(&streams.output)?;
    match ran {
        Ok(status) => assert_eq!(status, 0),
        Err(Error::FuelExhausted) => {
            return Err(ran_out(&tests.expectations, &streams.spent(fuel), fuel));
        }
        Err(error) => panic!("{error:?}"),
    }
    let failed = answered.failed.iter().map(said).collect();
    Ok((failed, count))
}

/// Where `failure` was written, and what it says: that, and what a
/// comparison saw.
fn said(failure: &faun_frontend::Failure<'_>) -> (String, String) {
    let at = written(failure.location);
    let saw = match &failure.sides {
        Some((faun_frontend::Side::Shown(left), faun_frontend::Side::Shown(right))) => {
            format!("\n  left:  {left}\n  right: {right}")
        }
        Some((faun_frontend::Side::Unshown(ty), _) | (_, faun_frontend::Side::Unshown(ty))) => {
            format!("\n  neither side is shown: `{ty}` has no `to_str`")
        }
        None => String::new(),
    };
    let said = format!("{at}: this expectation does not hold{saw}");
    (at, said)
}

/// Which expectation ran out of `fuel`, the steps they share, and what
/// each before it took: `spent` holds the latter, in order.
fn ran_out(
    expectations: &[faun_frontend::diagnostic::Location],
    spent: &[u64],
    fuel: u64,
) -> String {
    let Some(location) = expectations.get(spent.len()) else {
        return format!("the expectations ran out of their {fuel} steps after the last one");
    };
    let mut said = format!(
        "{}: this expectation ran out of fuel, the {fuel} steps of the reference \
         interpreter a file's expectations share",
        written(location)
    );
    let most = spent.iter().enumerate().max_by_key(|&(_, &steps)| steps);
    if let Some((at, steps)) = most {
        let before: u64 = spent.iter().sum();
        let _ = write!(
            said,
            "; the {} before it took {before}, the most {} with {steps}",
            spent.len(),
            written(&expectations[at])
        );
    }
    said
}

fn run_barb(barb: barb::Program, input: &[u8], errno: Option<u64>) -> (u32, String) {
    run_barb_fueled(barb, input, errno, 100_000_000)
}

fn run_barb_fueled(
    mut barb: barb::Program,
    input: &[u8],
    errno: Option<u64>,
    fuel: u64,
) -> (u32, String) {
    let mut streams = Streams {
        input: input.iter().copied().collect(),
        errno,
        ..Streams::default()
    };
    let status = run_on(&mut barb, &mut streams, fuel);
    (
        status,
        String::from_utf8(streams.output).expect("text written"),
    )
}

/// Run `barb` against `streams`: the status it exits with.
fn run_on(barb: &mut barb::Program, streams: &mut Streams, fuel: u64) -> u32 {
    try_run_spending(barb, streams, fuel)
        .unwrap_or_else(|error| panic!("{error:?}"))
        .0
}

/// The same, and how much of `fuel` it spent.
fn run_spending(barb: &mut barb::Program, streams: &mut Streams, fuel: u64) -> (u32, u64) {
    try_run_spending(barb, streams, fuel).unwrap_or_else(|error| panic!("{error:?}"))
}

/// The status, or why the interpreter stopped short.
fn try_run_on(barb: &mut barb::Program, streams: &mut Streams, fuel: u64) -> Result<u32, Error> {
    try_run_spending(barb, streams, fuel).map(|(status, _)| status)
}

/// The status and how much of `fuel` it spent, or why the interpreter
/// stopped short.
fn try_run_spending(
    barb: &mut barb::Program,
    streams: &mut Streams,
    fuel: u64,
) -> Result<(u32, u64), Error> {
    barb::optimize(barb);
    let machine = faun_core::lower_to_machine_ir(barb, &X86_64Linux.routines())
        .unwrap_or_else(|error| panic!("{error}"));
    let prepared = X86_64Linux
        .prepare(&machine)
        .unwrap_or_else(|error| panic!("{error}"));
    let main = prepared.entry();
    // `argc` is handed only where the program reads it.
    let handed = vec![BigUint::from(1u8); prepared.parameter_names(main).count()];
    let evaluation = evaluate::evaluate(
        &prepared,
        main,
        &handed,
        evaluate::Config {
            fuel,
            ..evaluate::Config::default()
        },
        streams,
    )?;
    let halted = evaluation.halted().expect("a program that exits");
    Ok((
        u32::try_from(&halted[0]).expect("a status"),
        fuel - evaluation.fuel_remaining,
    ))
}

impl Drop for Package {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A host with standard input to hand out, standard output to keep,
/// standard error to drop, and a directory of files to open, as Linux
/// answers each: a count or a descriptor, or `-errno`.
#[derive(Default)]
struct Streams {
    input: std::collections::VecDeque<u8>,
    output: Vec<u8>,
    /// What every write to standard output fails with, if it fails.
    errno: Option<u64>,
    files: Directory,
    /// Each descriptor past the standard three: the name it opened, where
    /// it reads or writes next, and whether it writes after the end.
    open: Vec<Option<Opened>>,
    /// How many times a descriptor past the standard three was read,
    /// written or closed when it was not open.
    misused: usize,
    /// The fuel left as each record separator, `0x1e`, was written to
    /// standard output: as each expectation finished, in a test build.
    records: Vec<u64>,
}

struct Opened {
    name: String,
    at: usize,
    append: bool,
}

/// Linux's `open` flags, as far as the host module asks for them.
const O_CREAT: u64 = 0o100;
const O_EXCL: u64 = 0o200;
const O_TRUNC: u64 = 0o1000;
const O_APPEND: u64 = 0o2000;

impl Streams {
    /// What each expectation took of `fuel`, from the fuel left as each
    /// record ended.
    fn spent(&self, fuel: u64) -> Vec<u64> {
        let mut left = fuel;
        self.records
            .iter()
            .map(|&now| {
                let took = left - now;
                left = now;
                took
            })
            .collect()
    }

    fn opened(&mut self, fd: u64) -> Option<&mut Opened> {
        let at = usize::try_from(fd.checked_sub(3)?).ok()?;
        let found = self.open.get_mut(at)?.as_mut();
        if found.is_none() {
            self.misused += 1;
        }
        found
    }

    /// A name opened as `flags` say: its descriptor, or the error.
    fn open(&mut self, name: &[u8], flags: u64) -> Result<u64, u64> {
        let name = String::from_utf8(name.to_vec()).map_err(|_| 22u64)?;
        // Beneath where the program runs, as `RESOLVE_BENEATH` answers.
        if name.starts_with('/') || name.split('/').any(|part| part == "..") {
            return Err(18);
        }
        match self.files.get_mut(&name) {
            Some(_) if flags & O_CREAT != 0 && flags & O_EXCL != 0 => return Err(17),
            Some(bytes) if flags & O_TRUNC != 0 => bytes.clear(),
            Some(_) => {}
            None if flags & O_CREAT != 0 => {
                self.files.insert(name.clone(), Vec::new());
            }
            None => return Err(2),
        }
        self.open.push(Some(Opened {
            name,
            at: 0,
            append: flags & O_APPEND != 0,
        }));
        Ok(u64::try_from(self.open.len()).expect("a descriptor") + 2)
    }

    /// Up to `asked` bytes from what `fd` names.
    fn take(&mut self, fd: u64, asked: usize) -> Result<Vec<u8>, u64> {
        if fd == 0 {
            return Ok((0..asked).map_while(|_| self.input.pop_front()).collect());
        }
        let opened = self.opened(fd).ok_or(9u64)?;
        let (name, from) = (opened.name.clone(), opened.at);
        let held = &self.files[&name];
        let from = from.min(held.len());
        let taken = held[from..(from + asked).min(held.len())].to_vec();
        self.opened(fd).expect("open").at = from + taken.len();
        Ok(taken)
    }

    /// `bytes` to what `fd` names, all of them.
    fn put(&mut self, fd: u64, bytes: &[u8]) -> Result<usize, u64> {
        match fd {
            1 if self.errno.is_some() => return Err(self.errno.expect("a failing write")),
            1 => self.output.extend_from_slice(bytes),
            2 => {}
            _ => {
                let opened = self.opened(fd).ok_or(9u64)?;
                let (name, append, from) = (opened.name.clone(), opened.append, opened.at);
                let held = self.files.get_mut(&name).expect("an open file");
                let from = if append { held.len() } else { from };
                let to = from + bytes.len();
                held.resize(held.len().max(to), 0);
                held[from..to].copy_from_slice(bytes);
                self.opened(fd).expect("open").at = to;
            }
        }
        Ok(bytes.len())
    }

    /// `fd` given up.
    fn close(&mut self, fd: u64) -> Result<u64, u64> {
        let at = usize::try_from(fd.checked_sub(3).ok_or(9u64)?).map_err(|_| 9u64)?;
        if let Some(opened @ Some(_)) = self.open.get_mut(at) {
            *opened = None;
            return Ok(0);
        }
        self.misused += 1;
        Err(9)
    }
}

impl Host for Streams {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        memory: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        let word = |value: &BigUint| u64::try_from(value).expect("a word");
        let count = |value: &BigUint| usize::try_from(word(value)).expect("a count");
        let answered = match name {
            "exit!" => return Ok(HostResult::Halt(args.to_vec())),
            // Up to as many as asked, where they are to lie: how many.
            "read_fd!" => self
                .take(word(&args[0]), count(&args[2]))
                .and_then(|taken| {
                    memory.write(word(&args[1]), &taken).map_err(|_| 14u64)?;
                    Ok(u64::try_from(taken.len()).expect("a count"))
                }),
            // All of it, every time: how many.
            "write_fd!" => {
                let bytes = memory.read(word(&args[1]), count(&args[2]))?.to_vec();
                if word(&args[0]) == 1 {
                    let ended = bytes.split(|&byte| byte == 0x1e).skip(1).count();
                    let fuel = memory.fuel_remaining();
                    self.records.extend(std::iter::repeat_n(fuel, ended));
                }
                self.put(word(&args[0]), &bytes)
                    .map(|went| u64::try_from(went).expect("a count"))
            }
            "open_at!" => {
                // A name is handed ended by a nought byte, as Linux reads it.
                let name = memory.read(word(&args[0]), count(&args[1]))?;
                let name = name.strip_suffix(&[0]).unwrap_or(name).to_vec();
                self.open(&name, word(&args[2]))
            }
            "fd_close!" => self.close(word(&args[0])),
            _ => return Err(Error::Host(name.to_owned())),
        };
        Ok(HostResult::Return(vec![BigUint::from(
            answered.unwrap_or_else(|errno| 0u64.wrapping_sub(errno)),
        )]))
    }
}
