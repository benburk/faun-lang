//! Effects, the definitions spelled with a `!`: only another effect may
//! call one, and a call of one stands on a line of its own, so the order
//! effects happen in is the order their lines are written in.

use super::failure;
use crate::declarations as n;
use crate::diagnostic::{Advised, Refusal};
use crate::hir as h;
use crate::{ModuleId, Symbol, Symbols};

/// Refuse the first effect called where it may not be.
pub(super) fn check(program: &n::Program, symbols: &Symbols) -> Result<(), Refusal> {
    for function in &program.functions {
        for clause in &function.clauses {
            in_clause(function.module, clause, symbols)?;
        }
    }
    Ok(())
}

/// Where an expression stands, which says whether an effect may be called
/// there.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Standing {
    /// At the top of a line of a body, or where such a line's value does.
    Alone,
    /// Inside an expression: an argument, an operand, a guard.
    Inside,
    /// On a line of a block that is itself inside an expression, which
    /// runs where, and whether, that expression works out the block.
    InBlockInside,
}

fn in_clause(module: ModuleId, clause: &h::Clause, symbols: &Symbols) -> Result<(), Refusal> {
    let effectful = symbols.text(clause.name).ends_with('!');
    if let Some(guard) = &clause.guard {
        expr(module, guard, effectful, Standing::Inside, symbols)?;
    }
    for binding in &clause.body.bindings {
        expr(module, &binding.value, effectful, Standing::Alone, symbols)?;
    }
    expr(
        module,
        &clause.body.result,
        effectful,
        Standing::Alone,
        symbols,
    )
}

fn expr(
    module: ModuleId,
    expression: &h::Expr,
    owner_effectful: bool,
    standing: Standing,
    symbols: &Symbols,
) -> Result<(), Refusal> {
    let effect = |name: Symbol| symbols.text(name).ends_with('!');
    let within =
        |inner: &h::Expr, standing| expr(module, inner, owner_effectful, standing, symbols);
    let called = |name| {
        call(
            module,
            expression.span,
            name,
            owner_effectful,
            standing,
            symbols,
        )
    };
    match &expression.kind {
        h::ExprKind::Global(name) if effect(*name) => Err(failure(
            module,
            expression.span,
            format!(
                "effect `{}` must be called and stand on its own",
                source_name(symbols, *name)
            ),
        )),
        // What `?` propagates, or `return` answers, stands where it does;
        // what `is` tests is worked out first, once, so it stands there too.
        h::ExprKind::Try(value) | h::ExprKind::Return(value) | h::ExprKind::Is(value, _) => {
            within(value, standing)
        }
        // A block's lines stand on their own where the block does, and its
        // answer where the block does. A block inside an expression is
        // worked out where, and only if, the expression works it out: on
        // the right of `&` or `|` on `Bool` perhaps not at all, so an
        // effect on one of its lines could be skipped.
        h::ExprKind::Block(body) => {
            let line = match standing {
                Standing::Alone => Standing::Alone,
                Standing::Inside | Standing::InBlockInside => Standing::InBlockInside,
            };
            for binding in &body.bindings {
                within(&binding.value, line)?;
            }
            within(&body.result, standing)
        }
        h::ExprKind::Call(head, arguments) => match &head.kind {
            h::ExprKind::Global(name) if effect(*name) => {
                called(*name)?;
                arguments
                    .iter()
                    .try_for_each(|argument| within(argument, Standing::Inside))
            }
            _ => expression.try_for_each_child(|inner| within(inner, Standing::Inside)),
        },
        h::ExprKind::Member(_, name) | h::ExprKind::Method(_, name, _, _) => {
            if effect(*name) {
                called(*name)?;
            }
            expression.try_for_each_child(|inner| within(inner, Standing::Inside))
        }
        h::ExprKind::Lambda(_, body) => expr(module, body, false, Standing::Inside, symbols),
        // An arm stands where the `is` does, as a branch does.
        h::ExprKind::Match(value, arms) => {
            within(value, standing)?;
            arms.iter().try_for_each(|arm| {
                if let Some(guard) = &arm.guard {
                    within(guard, Standing::Inside)?;
                }
                within(&arm.body, standing)
            })
        }
        // A condition is worked out first, once, and a branch is taken
        // after it: each stands where the `if` does.
        h::ExprKind::If(..) => expression.try_for_each_child(|inner| within(inner, standing)),
        _ => expression.try_for_each_child(|inner| within(inner, Standing::Inside)),
    }
}

fn call(
    module: ModuleId,
    span: crate::ast::Span,
    effect: Symbol,
    owner_effectful: bool,
    standing: Standing,
    symbols: &Symbols,
) -> Result<(), Refusal> {
    if !owner_effectful {
        return Err(failure(
            module,
            span,
            format!(
                "pure definitions cannot call effect `{}`",
                source_name(symbols, effect)
            ),
        ));
    }
    // An effect inside an expression would happen in an order the line's
    // reader must work out; standing alone, it happens where its line is.
    let refused = || {
        failure(
            module,
            span,
            format!(
                "effect `{}` must stand on its own",
                source_name(symbols, effect)
            ),
        )
    };
    match standing {
        Standing::Alone => Ok(()),
        Standing::Inside => Err(refused().label("inside an expression").help(
            "bind what it answers to a name on a line of its own, and use the name here",
        )),
        Standing::InBlockInside => Err(refused()
            .label("on a line of a block inside an expression")
            .note("a block inside an expression is worked out where the expression works it out, and on the right of `&` or `|` perhaps not at all")
            .help("move the line out of the block, before the line the block is in")),
    }
}

fn source_name(symbols: &Symbols, symbol: Symbol) -> &str {
    let spelled = symbols.spelling(symbol);
    spelled
        .rsplit_once('.')
        .map_or(spelled, |(_, member)| member)
}
