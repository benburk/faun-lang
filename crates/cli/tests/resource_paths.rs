//! Files handled at random, held to what each way through does with them.
//!
//! Each program opens one to three files and hands them to `run!`, whose
//! body reads them, closes them, hands them to helpers that close them or
//! only read them, closes two at once through a tuple or a list, puts them
//! in a tuple taken apart again, a chain of a declared recursive type or a
//! `Result`, and goes one way or another on a `Bool` it was handed. Each body
//! is made so that every way through uses up each file exactly once; some
//! are then broken on one way, by leaving something holding a file unused,
//! using it up again, or reading a file after it was used up or moved.
//!
//! Checking must refuse each broken program and accept each whole one, and
//! a whole one, run, must leave no file open and ask nothing of one it
//! closed. That a refused program is broken is known from how it was made;
//! that an accepted one is whole is also seen where it runs, so a checker
//! accepting what it should not is caught even where the making is wrong.

mod support;

use std::fmt::Write as _;

use faun_x86_64_linux::X86_64Linux;
use support::{Package, run_handling};

/// How many programs are written, unless `FAUN_RESOURCE_CASES` says.
const CASES: usize = 80;

/// What a name holds.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
    File,
    Tuple(Box<Self>, Box<Self>),
    /// A `Chain`, `[Link(File, Chain), End]`.
    Chain,
    /// A `Result(File, IoError)`.
    Result,
    /// A `Bundle`, `[Bound(Wrapper, File)]`, which a `Wrapper` may hold in
    /// turn: two types reaching each other, as one holding a file through
    /// the other does.
    Bundle,
    /// A `Wrapper`, `[Wrap(Bundle), Empty]`.
    Wrapper,
}

/// One line of a body, on what it names.
#[derive(Clone, Debug)]
enum Step {
    /// `f.read!(1)`, which lends the file.
    Read(String),
    /// `peek!(f)`, a helper that only reads it.
    Peek(String),
    /// `f.close!()`.
    Close(String),
    /// `close_it!(f)`, a helper that closes it.
    CloseVia(String),
    /// `close_both!((f, g))`.
    ClosePair(String, String),
    /// `close_all!([f, g, ...])`.
    CloseList(Vec<String>),
    /// `t = (a, b)`.
    Tuple(String, String, String),
    /// `(a, b) = t`.
    Split(String, String, String),
    /// `c = Link(f, End)`, or `Link(f, chain)` onto one held already.
    Link(String, String, Option<String>),
    /// `close_chain!(c)`.
    CloseChain(String),
    /// `r = Ok(f)`.
    Wrap(String, String),
    /// `release!(r)`.
    Release(String),
    /// `u = Bound(Empty, f)`.
    Bind(String, String),
    /// `w = Wrap(u)`.
    Wrap2(String, String),
    /// `close_bundle!(u)`.
    CloseBundle(String),
    /// `close_wrapper!(w)`.
    CloseWrapper(String),
}

impl Step {
    /// The names this uses up or moves into another.
    fn takes(&self) -> Vec<String> {
        match self {
            Self::Read(_) | Self::Peek(_) => Vec::new(),
            Self::Close(name)
            | Self::CloseVia(name)
            | Self::Split(name, _, _)
            | Self::CloseChain(name)
            | Self::Wrap(_, name)
            | Self::Release(name)
            | Self::Bind(_, name)
            | Self::Wrap2(_, name)
            | Self::CloseBundle(name)
            | Self::CloseWrapper(name) => vec![name.clone()],
            Self::ClosePair(first, second) | Self::Tuple(_, first, second) => {
                vec![first.clone(), second.clone()]
            }
            Self::CloseList(names) => names.clone(),
            Self::Link(_, file, onto) => {
                std::iter::once(file.clone()).chain(onto.clone()).collect()
            }
        }
    }

    /// Whether this uses what it takes up, rather than moving it on.
    const fn ends(&self) -> bool {
        matches!(
            self,
            Self::Close(_)
                | Self::CloseVia(_)
                | Self::ClosePair(..)
                | Self::CloseList(_)
                | Self::CloseChain(_)
                | Self::Release(_)
                | Self::CloseBundle(_)
                | Self::CloseWrapper(_)
        )
    }
}

/// Lines, then an answer or a way on for each of a `Bool`'s values.
#[derive(Clone, Debug)]
struct Block {
    steps: Vec<Step>,
    branch: Option<(usize, Box<Self>, Box<Self>)>,
}

/// How a whole body was broken.
#[derive(Clone, Copy, Debug)]
enum Broken {
    LeftOpen,
    UsedTwice,
    ReadMoved,
}

/// A generator of numbers that says the same each run.
struct Draw(u64);

impl Draw {
    const fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).expect("a small bound"))
            .expect("below a usize")
    }
}

/// The names a body holds, each with what it holds, and how many it has
/// named so far, so that each it makes is new.
struct Held<'a> {
    draw: &'a mut Draw,
    named: &'a mut usize,
}

impl Held<'_> {
    fn fresh(&mut self, kind: &Kind) -> String {
        *self.named += 1;
        let prefix = match kind {
            Kind::File => "f",
            Kind::Tuple(..) => "t",
            Kind::Chain => "k",
            Kind::Result => "r",
            Kind::Bundle => "u",
            Kind::Wrapper => "w",
        };
        format!("{prefix}{}", self.named)
    }

    /// One step on what `open` holds, which it updates.
    fn step(&mut self, open: &mut Vec<(String, Kind)>) -> Step {
        loop {
            // Types reaching each other are drawn twice as often: how one
            // holds a file through the other is the subtlest thing asked.
            let choice = self.draw.below(20);
            let drawn = match choice {
                0..=5 => self.on_files(choice, open),
                6..=11 => self.in_containers(choice, open),
                _ => self.in_bundles(choice % 4, open),
            };
            if let Some(step) = drawn {
                held_after(&step, open);
                return step;
            }
        }
    }

    /// One of the names `open` holds that `wanted` says of what they hold.
    fn one_of(&mut self, open: &[(String, Kind)], wanted: fn(&Kind) -> bool) -> Option<String> {
        let names: Vec<&String> = open
            .iter()
            .filter(|(_, kind)| wanted(kind))
            .map(|(name, _)| name)
            .collect();
        (!names.is_empty()).then(|| names[self.draw.below(names.len())].clone())
    }

    fn on_files(&mut self, choice: usize, open: &[(String, Kind)]) -> Option<Step> {
        let file = self.one_of(open, |kind| *kind == Kind::File)?;
        Some(match choice {
            0 => Step::Read(file),
            1 => Step::Peek(file),
            2 => Step::Close(file),
            3 => Step::CloseVia(file),
            4 => {
                let other = open
                    .iter()
                    .find(|(name, kind)| *kind == Kind::File && *name != file)?;
                Step::ClosePair(file, other.0.clone())
            }
            _ => Step::CloseList(
                open.iter()
                    .filter(|(_, kind)| *kind == Kind::File)
                    .filter(|_| self.draw.below(2) == 0)
                    .map(|(name, _)| name.clone())
                    .collect(),
            ),
        })
    }

    fn in_containers(&mut self, choice: usize, open: &[(String, Kind)]) -> Option<Step> {
        let file = |held: &mut Self| held.one_of(open, |kind| *kind == Kind::File);
        Some(match choice {
            6 if open.len() >= 2 => {
                let first = self.draw.below(open.len());
                let second = (first + 1 + self.draw.below(open.len() - 1)) % open.len();
                let kind = Kind::Tuple(
                    Box::new(open[first].1.clone()),
                    Box::new(open[second].1.clone()),
                );
                let name = self.fresh(&kind);
                Step::Tuple(name, open[first].0.clone(), open[second].0.clone())
            }
            7 => {
                let tuple = self.one_of(open, |kind| matches!(kind, Kind::Tuple(..)))?;
                let Some((_, Kind::Tuple(first, second))) =
                    open.iter().find(|(name, _)| *name == tuple)
                else {
                    unreachable!("a tuple is held as one")
                };
                let (first, second) = (*first.clone(), *second.clone());
                Step::Split(tuple, self.fresh(&first), self.fresh(&second))
            }
            8 => {
                let file = file(self)?;
                let onto = self
                    .one_of(open, |kind| *kind == Kind::Chain)
                    .filter(|_| self.draw.below(2) == 0);
                Step::Link(self.fresh(&Kind::Chain), file, onto)
            }
            9 => Step::CloseChain(self.one_of(open, |kind| *kind == Kind::Chain)?),
            10 => {
                let file = file(self)?;
                Step::Wrap(self.fresh(&Kind::Result), file)
            }
            11 => Step::Release(self.one_of(open, |kind| *kind == Kind::Result)?),
            _ => return None,
        })
    }

    fn in_bundles(&mut self, choice: usize, open: &[(String, Kind)]) -> Option<Step> {
        Some(match choice {
            0 => {
                let file = self.one_of(open, |kind| *kind == Kind::File)?;
                Step::Bind(self.fresh(&Kind::Bundle), file)
            }
            1 => {
                let bundle = self.one_of(open, |kind| *kind == Kind::Bundle)?;
                Step::Wrap2(self.fresh(&Kind::Wrapper), bundle)
            }
            2 => Step::CloseBundle(self.one_of(open, |kind| *kind == Kind::Bundle)?),
            _ => Step::CloseWrapper(self.one_of(open, |kind| *kind == Kind::Wrapper)?),
        })
    }

    /// Steps using up everything `open` holds.
    fn finish(&mut self, open: &mut Vec<(String, Kind)>) -> Vec<Step> {
        let mut steps = Vec::new();
        while let Some((name, kind)) = open.first().cloned() {
            let step = match kind {
                Kind::File if self.draw.below(2) == 0 => Step::Close(name),
                Kind::File => Step::CloseVia(name),
                Kind::Chain => Step::CloseChain(name),
                Kind::Result => Step::Release(name),
                Kind::Bundle => Step::CloseBundle(name),
                Kind::Wrapper => Step::CloseWrapper(name),
                Kind::Tuple(first, second) => {
                    Step::Split(name, self.fresh(&first), self.fresh(&second))
                }
            };
            held_after(&step, open);
            steps.push(step);
        }
        steps
    }

    /// A block using up each of `open` exactly once on every way through.
    fn whole(&mut self, mut open: Vec<(String, Kind)>, depth: usize) -> Block {
        let mut steps = Vec::new();
        for _ in 0..self.draw.below(5) {
            if open.is_empty() {
                break;
            }
            steps.push(self.step(&mut open));
        }
        if !open.is_empty() && depth > 0 && self.draw.below(2) == 0 {
            let condition = self.draw.below(2);
            let yes = self.whole(open.clone(), depth - 1);
            let no = self.whole(open, depth - 1);
            return Block {
                steps,
                branch: Some((condition, Box::new(yes), Box::new(no))),
            };
        }
        steps.extend(self.finish(&mut open));
        Block {
            steps,
            branch: None,
        }
    }
}

/// What `open` holds once `step` has been taken.
fn held_after(step: &Step, open: &mut Vec<(String, Kind)>) {
    let kind_of = |open: &[(String, Kind)], name: &str| {
        open.iter()
            .find(|(held, _)| held == name)
            .map(|(_, kind)| kind.clone())
            .expect("a name held")
    };
    let made = match step {
        Step::Tuple(name, first, second) => vec![(
            name.clone(),
            Kind::Tuple(
                Box::new(kind_of(open, first)),
                Box::new(kind_of(open, second)),
            ),
        )],
        Step::Split(tuple, first, second) => {
            let Kind::Tuple(first_kind, second_kind) = kind_of(open, tuple) else {
                unreachable!("only a tuple is split")
            };
            vec![(first.clone(), *first_kind), (second.clone(), *second_kind)]
        }
        Step::Link(name, _, _) => vec![(name.clone(), Kind::Chain)],
        Step::Wrap(name, _) => vec![(name.clone(), Kind::Result)],
        Step::Bind(name, _) => vec![(name.clone(), Kind::Bundle)],
        Step::Wrap2(name, _) => vec![(name.clone(), Kind::Wrapper)],
        _ => Vec::new(),
    };
    let taken = step.takes();
    open.retain(|(name, _)| !taken.contains(name));
    open.extend(made);
}

/// What uses up a name holding `kind` again, where a step after it would.
fn again(name: &str, kind: &Kind, named: &mut usize) -> Step {
    *named += 1;
    match kind {
        Kind::File => Step::Close(name.to_owned()),
        Kind::Chain => Step::CloseChain(name.to_owned()),
        Kind::Result => Step::Release(name.to_owned()),
        Kind::Bundle => Step::CloseBundle(name.to_owned()),
        Kind::Wrapper => Step::CloseWrapper(name.to_owned()),
        Kind::Tuple(..) => Step::Split(name.to_owned(), format!("x{named}"), format!("y{named}")),
    }
}

/// `block` broken on one way through, as `broken` says, where it can be.
/// `open` is what is held where the block begins.
fn break_one(
    draw: &mut Draw,
    block: &mut Block,
    mut open: Vec<(String, Kind)>,
    broken: Broken,
    named: &mut usize,
) -> bool {
    // What is held before each step, so that what a step takes is known.
    let mut before = Vec::with_capacity(block.steps.len());
    for step in &block.steps {
        before.push(open.clone());
        held_after(step, &mut open);
    }
    if let Some((_, yes, no)) = &mut block.branch
        && draw.below(2) == 0
    {
        let (first, second) = if draw.below(2) == 0 {
            (yes, no)
        } else {
            (no, yes)
        };
        if break_one(draw, first, open.clone(), broken, named)
            || break_one(draw, second, open, broken, named)
        {
            return true;
        }
    }
    let fits = |step: &Step, held: &[(String, Kind)]| match broken {
        Broken::LeftOpen => step.ends() && !step.takes().is_empty(),
        Broken::UsedTwice => !step.takes().is_empty(),
        Broken::ReadMoved => step.takes().iter().any(|name| {
            held.iter()
                .any(|(held, kind)| held == name && *kind == Kind::File)
        }),
    };
    let candidates: Vec<usize> = (0..block.steps.len())
        .filter(|&at| fits(&block.steps[at], &before[at]))
        .collect();
    if candidates.is_empty() {
        return false;
    }
    let at = candidates[draw.below(candidates.len())];
    break_at(draw, block, at, &before[at], broken, named);
    true
}

/// `block` broken at its step `at`, which `held` is what is held before.
fn break_at(
    draw: &mut Draw,
    block: &mut Block,
    at: usize,
    held: &[(String, Kind)],
    broken: Broken,
    named: &mut usize,
) {
    let taken = block.steps[at].takes();
    let is_file = |name: &String| {
        held.iter()
            .any(|(held, kind)| held == name && *kind == Kind::File)
    };
    match broken {
        Broken::LeftOpen => {
            block.steps.remove(at);
        }
        Broken::UsedTwice => {
            let name = &taken[draw.below(taken.len())];
            let kind = held
                .iter()
                .find(|(held, _)| held == name)
                .map(|(_, kind)| kind.clone())
                .expect("what a step takes is held");
            block.steps.insert(at + 1, again(name, &kind, named));
        }
        Broken::ReadMoved => {
            let file = taken
                .iter()
                .find(|name| is_file(name))
                .expect("a file taken");
            block.steps.insert(at + 1, Step::Read(file.clone()));
        }
    }
}

fn spelled_step(step: &Step, at: usize) -> String {
    match step {
        Step::Read(file) => format!("seen{at} = {file}.read!(1)"),
        Step::Peek(file) => format!("seen{at} = peek!({file})"),
        Step::Close(file) => format!("closed{at} = {file}.close!()"),
        Step::CloseVia(file) => format!("closed{at} = close_it!({file})"),
        Step::ClosePair(first, second) => format!("closed{at} = close_both!(({first}, {second}))"),
        Step::CloseList(files) => format!("closed{at} = close_all!([{}])", files.join(", ")),
        Step::Tuple(name, first, second) => format!("{name} = ({first}, {second})"),
        Step::Split(tuple, first, second) => format!("({first}, {second}) = {tuple}"),
        Step::Link(name, file, onto) => {
            format!(
                "{name} = Link({file}, {})",
                onto.as_deref().unwrap_or("End")
            )
        }
        Step::CloseChain(chain) => format!("closed{at} = close_chain!({chain})"),
        Step::Wrap(name, file) => format!("{name} = Ok({file})"),
        Step::Release(result) => format!("released{at} = release!({result})"),
        Step::Bind(name, file) => format!("{name} = Bound(Empty, {file})"),
        Step::Wrap2(name, bundle) => format!("{name} = Wrap({bundle})"),
        Step::CloseBundle(bundle) => format!("closed{at} = close_bundle!({bundle})"),
        Step::CloseWrapper(wrapper) => format!("closed{at} = close_wrapper!({wrapper})"),
    }
}

/// `block` as the lines of a body indented by `indent`, its last line its
/// answer; `next` numbers what each line binds.
fn spelled_block(block: &Block, indent: usize, next: &mut usize) -> String {
    let pad = " ".repeat(indent);
    let mut written = String::new();
    for step in &block.steps {
        *next += 1;
        writeln!(written, "{pad}{}", spelled_step(step, *next)).expect("writing to a string");
    }
    match &block.branch {
        None => writeln!(written, "{pad}0").expect("writing to a string"),
        Some((condition, yes, no)) => {
            let yes = spelled_block(yes, indent + 2, next);
            let no = spelled_block(no, indent + 2, next);
            writeln!(
                written,
                "{pad}if c{condition} then (\n{yes}{pad}) else (\n{no}{pad})"
            )
            .expect("writing to a string");
        }
    }
    written
}

/// The helpers every program may call, and the types holding files they
/// close.
const HELPERS: &str = "Chain : [Link(File, Chain), End]
Bundle : [Bound(Wrapper, File)]
Wrapper : [Wrap(Bundle), Empty]

close_bundle! : Bundle -> Nat
close_bundle!(Bound(inner, file)) -> (
  closed = file.close!()
  count = close_wrapper!(inner)
  count + 1
)

close_wrapper! : Wrapper -> Nat
close_wrapper!(Empty) -> 0
close_wrapper!(Wrap(bundle)) -> (
  count = close_bundle!(bundle)
  count
)

peek! : File -> Nat
peek!(file) -> (
  seen = file.read!(1)
  0
)

close_it! : File -> Nat
close_it!(file) -> (
  closed = file.close!()
  0
)

close_both! : ((File, File)) -> Nat
close_both!((first, second)) -> (
  a = first.close!()
  b = second.close!()
  0
)

close_all! : List(File) -> Nat
close_all!([]) -> 0
close_all!([file, *rest]) -> (
  closed = file.close!()
  count = close_all!(rest)
  count + 1
)

close_chain! : Chain -> Nat
close_chain!(End) -> 0
close_chain!(Link(file, rest)) -> (
  closed = file.close!()
  count = close_chain!(rest)
  count + 1
)

release! : Result(File, IoError) -> Nat
release!(Ok(file)) -> (
  closed = file.close!()
  0
)
release!(Err(_)) -> 0
";

/// Several as one: one alone, or a tuple of them.
fn tupled(parts: &[String]) -> String {
    match parts {
        [one] => one.clone(),
        many => format!("({})", many.join(", ")),
    }
}

fn program(files: usize, conditions: [bool; 2], body: &Block) -> String {
    let names =
        |prefix: &str| -> Vec<String> { (0..files).map(|at| format!("{prefix}{at}")).collect() };
    let mut written = format!(
        "import std.host {{File, IoError, Mode.*}}\n\n{HELPERS}\nrun! : ({}, Bool, Bool) -> Nat\n",
        vec!["File"; files].join(", ")
    );
    let mut next = 0;
    let body = spelled_block(body, 2, &mut next);
    let parameters = names("f0_").join(", ");
    write!(written, "run!({parameters}, c0, c1) -> (\n{body})\n\n").expect("writing");
    written.push_str(&start(files, conditions));
    written
}

/// `start!`, handing what `main!` opened to `run!` where all of it opened,
/// and `main!`.
fn start(files: usize, conditions: [bool; 2]) -> String {
    let names =
        |prefix: &str| -> Vec<String> { (0..files).map(|at| format!("{prefix}{at}")).collect() };
    let mut written = String::new();
    // A tuple of results is one parameter: `((A, B)) -> U8`.
    let results = vec!["Result(File, IoError)".to_owned(); files];
    let results = if files == 1 {
        results[0].clone()
    } else {
        format!("({})", tupled(&results))
    };
    writeln!(written, "start! : {results} -> U8").expect("writing");
    let [first, second] = conditions.map(|value| if value { "True" } else { "False" });
    let oks: Vec<String> = names("f")
        .iter()
        .map(|name| format!("Ok({name})"))
        .collect();
    write!(
        written,
        "start!({}) -> (\n  n = run!({}, {first}, {second})\n  U8.of_nat(n)\n)\n",
        tupled(&oks),
        names("f").join(", ")
    )
    .expect("writing");
    writeln!(written, "start!({}) -> (", tupled(&names("r"))).expect("writing");
    for at in 0..files {
        writeln!(written, "  released{at} = release!(r{at})").expect("writing");
    }
    written.push_str("  1\n)\n\n");
    written.push_str(&opening(files));
    written
}

/// `main!`, opening `files` files and handing them to `start!`.
fn opening(files: usize) -> String {
    let mut written = "main! : Host -> []\nmain!(host) -> (\n".to_owned();
    for at in 0..files {
        writeln!(
            written,
            "  o{at} = host.files.open!(\"f{at}.tmp\", Overwrite)"
        )
        .expect("writing");
    }
    let opened: Vec<String> = (0..files).map(|at| format!("o{at}")).collect();
    let opened = tupled(&opened);
    write!(
        written,
        "  status = start!({opened})\n  host.exit!(status)\n)\n"
    )
    .expect("writing");
    written
}

/// What checking says of the program at `entry`: `None` where it accepts,
/// and otherwise what it said, or what the compiler said where it broke.
fn refusal(entry: &std::path::Path) -> Option<String> {
    match std::panic::catch_unwind(|| faun::lower_to_barb(entry, &X86_64Linux)) {
        Ok(Ok(_)) => None,
        Ok(Err(error)) => Some(error.message),
        Err(_) => Some("the compiler broke".to_owned()),
    }
}

/// What is wrong of one program: refused where it is whole, accepted where
/// it is broken, or, accepted and run, a file left open or asked of after
/// it was closed.
fn judged(at: usize, source: &str, broken: Option<Broken>) -> Option<String> {
    let package = Package::new(&format!("resources-{at}"), source);
    let refused = refusal(&package.entry());
    match (refused, broken) {
        (Some(said), _) if said == "the compiler broke" => {
            Some(format!("{source}broke the compiler"))
        }
        (Some(_), Some(_)) => None,
        (Some(said), None) => Some(format!("{source}refused as `{said}`, where it is whole")),
        (None, Some(broken)) => Some(format!("{source}accepted, where it is broken: {broken:?}")),
        (None, None) => {
            let (status, handled) = run_handling(&package.entry());
            (status != 0 || handled.left_open != 0 || handled.misused != 0).then(|| {
                format!(
                    "{source}ran to {status}, leaving {} open and misusing {}",
                    handled.left_open, handled.misused
                )
            })
        }
    }
}

#[test]
fn every_way_through_uses_up_each_file_once() {
    let cases = std::env::var("FAUN_RESOURCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(CASES);
    let mut draw = Draw(0x2545_f491_4f6c_dd1d);
    let mut wrong = Vec::new();
    let (mut whole_seen, mut broken_seen) = (0, 0);
    for at in 0..cases {
        let (broken, source) = drawn_program(&mut draw);
        if broken.is_some() {
            broken_seen += 1;
        } else {
            whole_seen += 1;
        }
        wrong.extend(judged(at, &source, broken));
    }
    assert!(whole_seen > 0 && broken_seen > 0, "both kinds are drawn");
    assert!(
        wrong.is_empty(),
        "{} of {cases} programs disagree with how they were made:\n\n{}",
        wrong.len(),
        wrong.iter().take(4).cloned().collect::<Vec<_>>().join("\n")
    );
}

/// A program drawn whole, and broken where `broken` says how.
fn drawn_program(draw: &mut Draw) -> (Option<Broken>, String) {
    let files = 1 + draw.below(3);
    let open: Vec<(String, Kind)> = (0..files)
        .map(|file| (format!("f0_{file}"), Kind::File))
        .collect();
    let mut named = 0;
    let mut body = Held {
        draw,
        named: &mut named,
    }
    .whole(open.clone(), 2);
    let broken = match draw.below(4) {
        0 => Some(Broken::LeftOpen),
        1 => Some(Broken::UsedTwice),
        2 => Some(Broken::ReadMoved),
        _ => None,
    }
    .filter(|&broken| break_one(draw, &mut body, open, broken, &mut named));
    let conditions = [draw.below(2) == 0, draw.below(2) == 0];
    (broken, program(files, conditions, &body))
}
