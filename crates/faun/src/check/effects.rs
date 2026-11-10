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

fn in_clause(module: ModuleId, clause: &h::Clause, symbols: &Symbols) -> Result<(), Refusal> {
    let effectful = symbols.text(clause.name).ends_with('!');
    if let Some(guard) = &clause.guard {
        expr(module, guard, effectful, false, symbols)?;
    }
    for binding in &clause.body.bindings {
        expr(module, &binding.value, effectful, true, symbols)?;
    }
    expr(module, &clause.body.result, effectful, true, symbols)
}

fn expr(
    module: ModuleId,
    expression: &h::Expr,
    owner_effectful: bool,
    stands_alone: bool,
    symbols: &Symbols,
) -> Result<(), Refusal> {
    let effect = |name: Symbol| symbols.text(name).ends_with('!');
    let within =
        |inner: &h::Expr, stands_alone| expr(module, inner, owner_effectful, stands_alone, symbols);
    let called = |name| {
        call(
            module,
            expression.span,
            name,
            owner_effectful,
            stands_alone,
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
            within(value, stands_alone)
        }
        // A block's lines stand on their own, and its answer where the
        // block does.
        h::ExprKind::Block(body) => {
            for binding in &body.bindings {
                within(&binding.value, true)?;
            }
            within(&body.result, stands_alone)
        }
        h::ExprKind::Call(head, arguments) => match &head.kind {
            h::ExprKind::Global(name) if effect(*name) => {
                called(*name)?;
                arguments
                    .iter()
                    .try_for_each(|argument| within(argument, false))
            }
            _ => expression.try_for_each_child(|inner| within(inner, false)),
        },
        h::ExprKind::Member(_, name) | h::ExprKind::Method(_, name, _, _) => {
            if effect(*name) {
                called(*name)?;
            }
            expression.try_for_each_child(|inner| within(inner, false))
        }
        h::ExprKind::Lambda(_, body) => expr(module, body, false, false, symbols),
        // An arm stands where the `is` does, as a branch does.
        h::ExprKind::Match(value, arms) => {
            within(value, stands_alone)?;
            arms.iter().try_for_each(|arm| {
                if let Some(guard) = &arm.guard {
                    within(guard, false)?;
                }
                within(&arm.body, stands_alone)
            })
        }
        // A condition is worked out first, once, and a branch is taken
        // after it: each stands where the `if` does.
        h::ExprKind::If(..) => expression.try_for_each_child(|inner| within(inner, stands_alone)),
        _ => expression.try_for_each_child(|inner| within(inner, false)),
    }
}

fn call(
    module: ModuleId,
    span: crate::ast::Span,
    effect: Symbol,
    owner_effectful: bool,
    stands_alone: bool,
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
    if !stands_alone {
        return Err(failure(
            module,
            span,
            format!(
                "effect `{}` must stand on its own",
                source_name(symbols, effect)
            ),
        )
        .label("inside an expression")
        .help("bind what it answers to a name on a line of its own, and use the name here"));
    }
    Ok(())
}

fn source_name(symbols: &Symbols, symbol: Symbol) -> &str {
    let spelled = symbols.spelling(symbol);
    spelled
        .rsplit_once('.')
        .map_or(spelled, |(_, member)| member)
}
