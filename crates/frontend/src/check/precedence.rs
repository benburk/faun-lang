//! What a refusal at a bitwise operator's operand says of precedence.
//!
//! `&`, `|` and `^` bind looser than the comparisons, so a mask test
//! written as C writes it unparenthesized, `flags & 4 == 0`, is
//! `flags & (4 == 0)`: a `Nat` and a `Bool` handed to one `and`. The
//! refusal is a type's, at the operand, and says nothing of why; where it
//! falls on the operand of a bitwise operator one of whose sides is a
//! comparison written without parentheses, this adds the reading the author
//! likely meant.

use crate::ast::{BinaryOp, Span};
use crate::context::Context;
use crate::declarations as n;
use crate::diagnostic::{Advised, Refusal};
use crate::hir as h;

/// `refused`, with what to write instead where it falls on the right of a
/// bitwise operator whose other side, or whose right, is an unparenthesized
/// comparison.
pub(super) fn hinted(mut refused: Refusal, program: &n::Program, cx: &Context) -> Refusal {
    let Some((module, at)) = refused.at else {
        return refused;
    };
    let text = cx.source(module).text();
    let mut found = None;
    for function in program.functions.iter().filter(|f| f.module == module) {
        for clause in &function.clauses {
            let body = clause.body.exprs().chain(clause.guard.as_ref());
            for expression in body {
                if found.is_none() {
                    found = hint(expression, at, text);
                }
            }
        }
    }
    if let Some(help) = found {
        // What a refusal of its own would advise, such as converting a
        // numeral, does not apply to an operand the author did not mean.
        refused.advice.help.clear();
        refused = refused.help(help);
    }
    refused
}

/// What to write for the bitwise operator in `expression` whose right
/// operand is at `at`, where one side is a comparison.
fn hint(expression: &h::Expr, at: Span, text: &str) -> Option<String> {
    if let h::ExprKind::Binary(operator, left, right) = &expression.kind
        && let Some(bitwise) = bitwise(*operator)
        && right.span == at
    {
        let written = |span: Span| span.text(text);
        // A shift beside the bitwise operator takes parentheses with it.
        let beside = |side: &h::Expr| {
            let written = side.span.text(text);
            if shifts(side, text) {
                format!("({written})")
            } else {
                written.to_owned()
            }
        };
        // `flags & 4 == 0`, read `flags & (4 == 0)`.
        if let Some((compared, (low, high))) = comparison(right, text) {
            let fix = format!(
                "({} {bitwise} {}) {compared} {}",
                written(left.span),
                beside(low),
                written(high.span)
            );
            return Some(told(bitwise, compared, &fix));
        }
        // `0 == flags & 4`, read `(0 == flags) & 4`.
        if let Some((compared, (low, high))) = comparison(left, text) {
            let fix = format!(
                "{} {compared} ({} {bitwise} {})",
                written(low.span),
                beside(high),
                written(right.span)
            );
            return Some(told(bitwise, compared, &fix));
        }
    }
    let mut found = None;
    expression.for_each_child(|child| {
        if found.is_none() {
            found = hint(child, at, text);
        }
    });
    found
}

fn told(bitwise: &str, compared: &str, fix: &str) -> String {
    format!("`{bitwise}` binds looser than `{compared}`: write `{fix}`")
}

const fn bitwise(operator: BinaryOp) -> Option<&'static str> {
    match operator {
        BinaryOp::And => Some("&"),
        BinaryOp::Or => Some("|"),
        BinaryOp::Xor => Some("^"),
        _ => None,
    }
}

/// Whether `expression` is a shift written without parentheses.
fn shifts(expression: &h::Expr, text: &str) -> bool {
    matches!(
        expression.kind,
        h::ExprKind::Binary(BinaryOp::ShiftLeft | BinaryOp::ShiftRight, ..)
    ) && !parenthesized(expression.span.text(text))
}

/// The operator of a comparison written without parentheses, and its two
/// sides.
fn comparison<'a>(
    expression: &'a h::Expr,
    text: &str,
) -> Option<(&'static str, (&'a h::Expr, &'a h::Expr))> {
    let h::ExprKind::Binary(operator, left, right) = &expression.kind else {
        return None;
    };
    let compared = match operator {
        BinaryOp::Equal => "==",
        BinaryOp::NotEqual => "!=",
        BinaryOp::Less => "<",
        BinaryOp::LessEqual => "<=",
        BinaryOp::Greater => ">",
        BinaryOp::GreaterEqual => ">=",
        _ => return None,
    };
    if parenthesized(expression.span.text(text)) {
        return None;
    }
    Some((compared, (&**left, &**right)))
}

/// Whether `written` is one parenthesized expression: its first `(`
/// closes at its end, as in `(4 == 0)` and not `(a) == (b)`.
fn parenthesized(written: &str) -> bool {
    if !written.starts_with('(') {
        return false;
    }
    let mut depth = 0usize;
    for (at, character) in written.char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return at + 1 == written.len();
                }
            }
            _ => {}
        }
    }
    false
}
