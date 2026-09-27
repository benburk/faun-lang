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
    let span = Span::new(written, written);
    let sites = &mut resolved.sites;
    let symbols = &mut resolved.symbols;
    let (print, exit, select, to_str) = (
        symbols.intern("print!"),
        symbols.intern("exit!"),
        symbols.intern("select"),
        symbols.intern("to_str"),
    );
    let failures = failures(sites, span, asked, select, to_str);
    let text = sites.expr(span, h::ExprKind::String(failures));
    let receiver = sites.expr(span, h::ExprKind::Local(h::LocalId(0)));
    let printed = sites.expr(
        span,
        h::ExprKind::Method(Box::new(receiver), print, vec![text]),
    );
    let status = sites.expr(span, h::ExprKind::Number(0u8.into()));
    let receiver = sites.expr(span, h::ExprKind::Local(h::LocalId(0)));
    let exited = sites.expr(
        span,
        h::ExprKind::Method(Box::new(receiver), exit, vec![status]),
    );
    h::Clause {
        site: sites.fresh(),
        span,
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
fn failures(
    sites: &mut h::Sites,
    span: Span,
    asked: &[Symbol],
    select: Symbol,
    to_str: Symbol,
) -> Vec<h::StringPart> {
    let mut failures = Vec::with_capacity(asked.len());
    for (number, &expectation) in asked.iter().enumerate() {
        let called = sites.expr(span, h::ExprKind::Global(expectation));
        let held = sites.expr(span, h::ExprKind::Call(Box::new(called), Vec::new()));
        let nothing = sites.expr(span, h::ExprKind::String(Vec::new()));
        let numbered = sites.expr(
            span,
            h::ExprKind::String(vec![h::StringPart::Text(
                format!("{} ", number + 1).into_bytes(),
            )]),
        );
        let selected = sites.expr(
            span,
            h::ExprKind::Method(Box::new(held), select, vec![nothing, numbered]),
        );
        let text = sites.expr(
            span,
            h::ExprKind::Method(Box::new(selected), to_str, Vec::new()),
        );
        failures.push(h::StringPart::Splice(text));
    }
    failures
}
