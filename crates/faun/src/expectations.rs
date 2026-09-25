//! The entry `faun test` builds: one that asks every expectation in the
//! entry's package and says which do not hold.
//!
//! Resolution has already made each `expect` a definition answering a
//! `Bool`. The test entry is the build's entry in place of the package's
//! `main!`, which is still checked as any definition is, and is what this
//! would be, were its names writable:
//!
//! ```text
//! expect main!(host) ->
//!   host.print!("${expect_1().select("" "1 ")}${expect_2().select("" "2 ")}")
//!   host.exit!(0)
//! ```
//!
//! So what it prints is the number of each expectation that does not hold,
//! counted from one across the package in the order its modules were loaded,
//! each followed by a space; printing nothing is every one holding. Every
//! expectation is asked whichever others fail, and what the compiler settles
//! while compiling is settled before the program runs.

use crate::Symbol;
use crate::ast::Span;
use crate::diagnostic::Location;
use crate::hir as h;
use crate::host::{HostIds, Main};
use crate::modules::LoadedProgram;
use crate::resolve::ResolvedProgram;

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

/// Make `main` the test entry, answering where each expectation it asks was
/// written, in the order it numbers them.
pub(crate) fn enter(resolved: &mut ResolvedProgram, host: &HostIds, main: &Main) -> Vec<Location> {
    let (asked, locations) = asked(resolved);
    let clause = entry(resolved, main, &asked);
    let spelling = resolved.symbols.intern("expect main!");
    let module = resolved
        .program
        .modules
        .iter_mut()
        .find(|module| module.source == main.module)
        .expect("the entry module was resolved");
    module.items.push(h::Item::Signature(h::SignatureDecl {
        span: clause.span,
        name: main.symbol,
        spelling,
        parameters: vec![h::Type::Named(host.host, Vec::new())],
        result: h::Type::Variants(Vec::new()),
        constraints: Vec::new(),
    }));
    module.items.push(h::Item::Clause(clause));
    locations
}

/// Every expectation in the package, in the order the test entry numbers
/// them, and where each was written.
fn asked(resolved: &ResolvedProgram) -> (Vec<Symbol>, Vec<Location>) {
    let mut asked = Vec::new();
    let mut locations = Vec::new();
    for module in &resolved.program.modules {
        if !resolved.package.contains(&module.source) {
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
            locations.push(resolved.location(module.source, span));
            asked.push(expectation);
        }
    }
    (asked, locations)
}

/// The test entry's one clause, asking each of `asked`.
fn entry(resolved: &mut ResolvedProgram, main: &Main, asked: &[Symbol]) -> h::Clause {
    let written = resolved.source(main.module).text().len();
    let mut places = Places(written);
    let symbols = &mut resolved.symbols;
    let (print, exit, select) = (
        symbols.intern("print!"),
        symbols.intern("exit!"),
        symbols.intern("select"),
    );
    let failures = failures(&mut places, asked, select);
    let text = places.at(h::ExprKind::String(failures));
    let receiver = places.at(h::ExprKind::Local(h::LocalId(0)));
    let printed = places.at(h::ExprKind::Method(Box::new(receiver), print, vec![text]));
    let status = places.at(h::ExprKind::Number(0u8.into()));
    let receiver = places.at(h::ExprKind::Local(h::LocalId(0)));
    let exited = places.at(h::ExprKind::Method(Box::new(receiver), exit, vec![status]));
    h::Clause {
        span: Span::new(written, places.0 + 1),
        name: main.symbol,
        patterns: vec![h::Pattern::Bind(h::LocalId(0))],
        guard: None,
        body: h::Body {
            bindings: vec![h::Binding {
                pattern: h::Pattern::Wild,
                value: printed,
            }],
            result: exited,
        },
        locals: 1,
    }
}

/// A splice for each of `asked`, of nothing where it holds and of its
/// number and a space where it does not.
fn failures(places: &mut Places, asked: &[Symbol], select: Symbol) -> Vec<h::StringPart> {
    let mut failures = Vec::with_capacity(asked.len());
    for (number, &expectation) in asked.iter().enumerate() {
        let called = places.at(h::ExprKind::Global(expectation));
        let held = places.at(h::ExprKind::Call(Box::new(called), Vec::new()));
        let nothing = places.at(h::ExprKind::String(Vec::new()));
        let numbered = places.at(h::ExprKind::String(vec![h::StringPart::Text(
            format!("{} ", number + 1).into_bytes(),
        )]));
        failures.push(h::StringPart::Splice(places.at(h::ExprKind::Method(
            Box::new(held),
            select,
            vec![nothing, numbered],
        ))));
    }
    failures
}

/// Where the next expression the test entry makes is placed.
///
/// Checking records what it learns of each expression by where it was
/// written, so each is given a place of its own past the end of the entry's
/// source, where nothing was written. Each is one byte wide: checking keeps
/// the empty place where a splice starts for the `to_str` it calls.
struct Places(usize);

impl Places {
    fn at(&mut self, kind: h::ExprKind) -> h::Expr {
        self.0 += 1;
        h::Expr {
            span: Span::new(self.0, self.0 + 1),
            kind,
        }
    }
}
