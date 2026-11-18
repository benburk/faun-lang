//! The entry `faun test` builds: one that asks every expectation in the
//! entry's package and says which do not hold, and what each comparison
//! that does not hold saw.
//!
//! Resolution has already made each `expect` a definition answering a
//! `Bool`. The test entry is the build's entry in place of the package's
//! `main!`, which is still checked as any definition is, and is what this
//! would be, were its names writable:
//!
//! ```text
//! expect main!(host) ->
//!   host.print!("${expect_1().select("" "1-␞")}${expect_2()}")
//!   host.exit!(0)
//! ```
//!
//! So what it prints is a record for each expectation that does not hold,
//! each ended by a record separator, `␞` (`0x1e`): its number, counted from
//! one across the package in the order its modules were loaded, and `-`.
//! Printing nothing is every one holding. An expectation whose last line
//! is a comparison, `expect a == b` or any of `!=`, `<`, `<=`, `>` and
//! `>=`, answers its record itself, with both sides after it, each after a
//! unit separator, `␟` (`0x1f`):
//!
//! ```text
//! expect_2() -> (a, b) is ((left, right) -> if left == right then "" else "2-␟${left}␟${right}␞")
//! ```
//!
//! A side is written by its `to_str`, and where its type has none, by a
//! nought byte and that type's name, rather than the build being refused:
//! see [`crate::hir::Sites::show`]. [`crate::Tests::answered`] reads the
//! records back.
//!
//! [`Reporting::Each`] prints a record for every expectation, a held one's
//! number and `+`, each as soon as it is asked: whoever runs it can tell
//! which expectation was being asked when the program stopped, and what
//! each before it cost. Every expectation is asked whichever others fail,
//! and what the compiler settles while compiling is settled before the
//! program runs.

use crate::Symbol;
use crate::ast::{BinaryOp, Span};
use crate::context::Context;
use crate::diagnostic::Location;
use crate::hir as h;
use crate::host::Main;
use crate::modules::LoadedProgram;

/// Which expectations the test entry prints a record of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reporting {
    /// Only those that do not hold, all at once when every one is asked.
    Failures,
    /// Every one, each as soon as it is asked.
    Each,
}

/// Ends each record the test entry prints.
pub(crate) const RECORD: u8 = 0x1e;
/// Comes before each side of a comparison that does not hold.
pub(crate) const UNIT: u8 = 0x1f;

/// The entry a test build enters by: a definition of the entry module that
/// no source can name, since its name holds a space.
pub(crate) fn main(loaded: &mut LoadedProgram) -> Main {
    let entry = loaded.module(loaded.entry);
    let name = format!("{}$$expect main!", loaded.symbols.text(entry.namespace));
    Main {
        module: loaded.entry,
        symbol: loaded.symbols.intern(&name),
    }
}

/// `program` with `main` the test entry, and where each expectation it asks
/// was written, in the order it numbers them.
pub(crate) fn enter(
    mut program: h::Program,
    cx: &mut Context,
    main: &Main,
    reporting: Reporting,
) -> (h::Program, Vec<Location>) {
    let (asked, locations) = asked(&program, cx);
    let mut records = Vec::with_capacity(asked.len());
    for (at, &expectation) in asked.iter().enumerate() {
        let record = Record {
            number: at + 1,
            reporting,
        };
        let shows = shows_sides(&mut program, cx, expectation, &record);
        records.push((expectation, record, shows));
    }
    let clause = entry(cx, main, &records, reporting);
    let spelling = cx.symbols.intern("expect main!");
    let module = program
        .modules
        .iter_mut()
        .find(|module| module.source == main.module)
        .expect("the entry module was resolved");
    module
        .items
        .push(cx.host.entry_signature(clause.span, main.symbol, spelling));
    module.items.push(h::Item::Clause(clause));
    (program, locations)
}

/// Every expectation in the package, in the order the test entry numbers
/// them, and where each was written.
fn asked(program: &h::Program, cx: &Context) -> (Vec<Symbol>, Vec<Location>) {
    let mut asked = Vec::new();
    let mut locations = Vec::new();
    for module in &program.modules {
        if !cx.package.contains(&module.source) {
            continue;
        }
        for &expectation in &module.expectations {
            let span = module
                .items
                .iter()
                .find_map(|item| match item {
                    h::Item::Clause(clause) if clause.name == expectation => Some(clause.span),
                    _ => None,
                })
                .expect("an expectation is a clause of its module");
            locations.push(cx.location(module.source, span));
            asked.push(expectation);
        }
    }
    (asked, locations)
}

/// What one expectation's record says.
struct Record {
    number: usize,
    reporting: Reporting,
}

impl Record {
    /// What it prints where it holds.
    fn held(&self) -> Vec<u8> {
        match self.reporting {
            Reporting::Failures => Vec::new(),
            Reporting::Each => self.ended("+"),
        }
    }

    /// Its number and `mark`, ended.
    fn ended(&self, mark: &str) -> Vec<u8> {
        let mut text = format!("{}{mark}", self.number).into_bytes();
        text.push(RECORD);
        text
    }
}

/// Make `expectation`, where its last line is a comparison, answer its own
/// record, both sides shown where it does not hold; whether it does.
fn shows_sides(
    program: &mut h::Program,
    cx: &mut Context,
    expectation: Symbol,
    record: &Record,
) -> bool {
    let str_ = cx.prelude.str_;
    let defines =
        |item: &h::Item| matches!(item, h::Item::Clause(clause) if clause.name == expectation);
    let Some(module) = program
        .modules
        .iter_mut()
        .find(|module| module.items.iter().any(defines))
    else {
        return false;
    };
    let mut shown = false;
    for item in &mut module.items {
        if let h::Item::Clause(clause) = item
            && clause.name == expectation
        {
            shown |= answer_record(clause, cx, record);
        }
    }
    if shown {
        for item in &mut module.items {
            if let h::Item::Signature(signature) = item
                && signature.name == expectation
            {
                signature.result = h::Type::Named(str_, Vec::new());
            }
        }
    }
    shown
}

/// Whether `operator` compares.
const fn compares(operator: BinaryOp) -> bool {
    matches!(
        operator,
        BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual
    )
}

/// Make `clause`, an expectation, answer `record` where its last line is a
/// comparison: `a == b` becomes
/// `(a, b) is ((x, y) -> if x == y then held else failed)`, its two
/// locals the clause's next. Whether it was one.
fn answer_record(clause: &mut h::Clause, cx: &mut Context, record: &Record) -> bool {
    let to_str = cx.symbols.intern("to_str");
    let locals = clause.locals;
    let last = last_line(&mut clause.body.result);
    if !matches!(last.kind, h::ExprKind::Binary(operator, ..) if compares(operator)) {
        return false;
    }
    let placeholder = h::ExprKind::Tuple(Vec::new());
    let h::ExprKind::Binary(operator, first, second) =
        std::mem::replace(&mut last.kind, placeholder)
    else {
        unreachable!("matched above")
    };
    let both = Sides {
        spans: (first.span, second.span),
        locals: (h::LocalId(locals), h::LocalId(locals + 1)),
        to_str,
    };
    let span = last.span;
    let pair = cx
        .sites
        .expr(span, h::ExprKind::Tuple(vec![*first, *second]));
    let arm = arm(&mut cx.sites, (span, operator), &both, record);
    last.kind = h::ExprKind::Match(Box::new(pair), vec![arm]);
    clause.locals += 2;
    true
}

/// The one arm of a comparison's record: its sides bound, compared by
/// `operator` as written at `span`, and the record its answer says.
fn arm(
    sites: &mut h::Sites,
    (span, operator): (Span, BinaryOp),
    both: &Sides,
    record: &Record,
) -> h::Arm {
    let x = sites.expr(both.spans.0, h::ExprKind::Local(both.locals.0));
    let y = sites.expr(both.spans.1, h::ExprKind::Local(both.locals.1));
    let compared = sites.expr(
        span,
        h::ExprKind::Binary(operator, Box::new(x), Box::new(y)),
    );
    let held = sites.expr(span, text(record.held()));
    let failed = failed(sites, span, both, record);
    let answer = sites.expr(
        span,
        h::ExprKind::If(Box::new(compared), Box::new(held), Box::new(failed)),
    );
    let pattern = h::Pattern::Tuple(vec![
        h::Pattern::Bind(both.locals.0),
        h::Pattern::Bind(both.locals.1),
    ]);
    h::Arm {
        pattern,
        guard: None,
        body: answer,
    }
}

/// Where a comparison's two sides were written, the locals they are bound
/// to, and the member that writes each.
struct Sides {
    spans: (Span, Span),
    locals: (h::LocalId, h::LocalId),
    to_str: Symbol,
}

/// The last line of `result`, inside any block it is.
fn last_line(mut result: &mut h::Expr) -> &mut h::Expr {
    while matches!(result.kind, h::ExprKind::Block(_)) {
        let h::ExprKind::Block(body) = &mut result.kind else {
            unreachable!("matched above")
        };
        result = &mut body.result;
    }
    result
}

/// A string of `bytes`.
fn text(bytes: Vec<u8>) -> h::ExprKind {
    if bytes.is_empty() {
        return h::ExprKind::String(Vec::new());
    }
    h::ExprKind::String(vec![h::StringPart::Text(bytes)])
}

/// The record of a comparison that does not hold: its number, `-`, and
/// each side by its `to_str`.
fn failed(sites: &mut h::Sites, span: Span, both: &Sides, record: &Record) -> h::Expr {
    let mut side = |local, place| {
        let value = sites.expr(place, h::ExprKind::Local(local));
        let written = sites.expr(
            place,
            h::ExprKind::Method(Box::new(value), both.to_str, place, Vec::new()),
        );
        sites.show(written.site);
        h::StringPart::Splice(written)
    };
    let first = side(both.locals.0, both.spans.0);
    let second = side(both.locals.1, both.spans.1);
    let opening = [format!("{}-", record.number).into_bytes(), vec![UNIT]].concat();
    let parts = vec![
        h::StringPart::Text(opening),
        first,
        h::StringPart::Text(vec![UNIT]),
        second,
        h::StringPart::Text(vec![RECORD]),
    ];
    sites.expr(span, h::ExprKind::String(parts))
}

/// The test entry's one clause, printing each of `records`.
fn entry(
    cx: &mut Context,
    main: &Main,
    records: &[(Symbol, Record, bool)],
    reporting: Reporting,
) -> h::Clause {
    let written = cx.source(main.module).text().len();
    let span = Span::new(written, written);
    let (print, exit, select) = (
        cx.symbols.intern("print!"),
        cx.symbols.intern("exit!"),
        cx.symbols.intern("select"),
    );
    let sites = &mut cx.sites;
    let parts = records
        .iter()
        .map(|(expectation, record, shows)| {
            let said = said(sites, span, *expectation, record, *shows, select);
            h::StringPart::Splice(said)
        })
        .collect::<Vec<_>>();
    let lines: Vec<Vec<h::StringPart>> = match reporting {
        Reporting::Failures => vec![parts],
        Reporting::Each => parts.into_iter().map(|part| vec![part]).collect(),
    };
    let bindings = lines
        .into_iter()
        .map(|line| printing(sites, span, print, line))
        .collect();
    let status = sites.expr(span, h::ExprKind::Number(0u8.into()));
    let receiver = sites.expr(span, h::ExprKind::Local(h::LocalId(0)));
    let exited = h::ExprKind::Method(Box::new(receiver), exit, span, vec![status]);
    let exited = sites.expr(span, exited);
    h::Clause {
        site: sites.fresh(),
        span,
        name: main.symbol,
        patterns: vec![h::Pattern::Bind(h::LocalId(0))],
        guard: None,
        body: h::Body {
            bindings,
            result: exited,
        },
        locals: 1,
    }
}

/// What `expectation` prints: its own answer where it `shows` its sides,
/// and otherwise its `Bool` read as `record` says.
fn said(
    sites: &mut h::Sites,
    span: Span,
    expectation: Symbol,
    record: &Record,
    shows: bool,
    select: Symbol,
) -> h::Expr {
    let called = sites.expr(span, h::ExprKind::Global(expectation));
    let answered = sites.expr(span, h::ExprKind::Call(Box::new(called), Vec::new()));
    if shows {
        return answered;
    }
    let held = sites.expr(span, text(record.held()));
    let failed = sites.expr(span, text(record.ended("-")));
    sites.expr(
        span,
        h::ExprKind::Method(Box::new(answered), select, span, vec![held, failed]),
    )
}

/// A line of the test entry printing `line`, handed the host as its first
/// local.
fn printing(
    sites: &mut h::Sites,
    span: Span,
    print: Symbol,
    line: Vec<h::StringPart>,
) -> h::Binding {
    let text = sites.expr(span, h::ExprKind::String(line));
    let receiver = sites.expr(span, h::ExprKind::Local(h::LocalId(0)));
    let printed = sites.expr(
        span,
        h::ExprKind::Method(Box::new(receiver), print, span, vec![text]),
    );
    h::Binding {
        pattern: h::Pattern::Wild,
        value: printed,
    }
}
