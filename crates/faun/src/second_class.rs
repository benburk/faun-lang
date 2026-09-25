//! Functions are higher-order but second-class, as in Ori: a named function
//! or a lambda is passed straight into a call, and nothing else. It is never
//! bound with `=`, answered, or stored in data, so every value a program
//! holds is first-order data and every call a static edge.
//!
//! Checked on the specialized program, where every type is concrete: a type
//! variable a caller fills with a function is caught where the function
//! would be held.

use crate::specialize::{Body, Clause, Expr, ExprKind, Program, SpecializeError, Type};

/// Refuse the first function value held anywhere but a call's argument.
pub(crate) fn check(program: &Program) -> Result<(), SpecializeError> {
    for function in &program.functions {
        for Clause { guard, body, .. } in &function.clauses {
            if let Some(guard) = guard {
                value(guard, false)?;
            }
            self::body(body)?;
        }
    }
    Ok(())
}

fn body(body: &Body) -> Result<(), SpecializeError> {
    for binding in &body.bindings {
        value(&binding.value, false)?;
    }
    value(&body.result, false)
}

/// Check `expression`, which is a call's argument or head when `passed`.
fn value(expression: &Expr, passed: bool) -> Result<(), SpecializeError> {
    if let Type::Function(parameters, _) = &expression.ty {
        if parameters.is_empty() {
            return Err(located(
                expression,
                "a definition with no parameters is a value, reached as `name()`",
            ));
        }
        if !passed {
            return Err(located(
                expression,
                "a function may only be passed straight into a call; it cannot be bound, answered, or stored",
            ));
        }
    }
    match &expression.kind {
        ExprKind::Local(_)
        | ExprKind::Function(_)
        | ExprKind::ConstructorFunction(_)
        | ExprKind::Natural(_) => Ok(()),
        ExprKind::Construct(_, fields) => fields.iter().try_for_each(|field| value(field, false)),
        ExprKind::Record(fields) => fields.iter().try_for_each(|(_, field)| value(field, false)),
        ExprKind::Update(base, fields) => {
            value(base, false)?;
            fields.iter().try_for_each(|(_, field)| value(field, false))
        }
        ExprKind::Tuple(members) => members.iter().try_for_each(|member| value(member, false)),
        ExprKind::Project(receiver, _) => value(receiver, false),
        ExprKind::DirectCall(_, arguments) => arguments
            .iter()
            .try_for_each(|argument| value(argument, true)),
        ExprKind::Invoke(head, arguments) => {
            value(head, true)?;
            arguments
                .iter()
                .try_for_each(|argument| value(argument, true))
        }
        ExprKind::Lambda(_, result) => value(result, false),
        ExprKind::Widen(inner) => value(inner, passed),
        ExprKind::Try(inner) => value(inner, false),
    }
}

fn located(expression: &Expr, message: &str) -> SpecializeError {
    SpecializeError {
        message: message.to_owned(),
        at: Some((expression.module, expression.span)),
    }
}
