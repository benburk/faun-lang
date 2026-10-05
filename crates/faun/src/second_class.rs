//! Functions are higher-order but second-class, as in Ori: a named function
//! or a lambda is passed straight into a call, and nothing else. It is never
//! bound with `=`, answered, or stored in data, so every value a program
//! holds is first-order data and every call a static edge.
//!
//! Checked on the specialized program, where every type is concrete: a type
//! variable a caller fills with a function is caught where the function
//! would be held. Where that is outside the package, in a definition it
//! depends on, the package's call that handed the function on is blamed.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::ModuleId;
use crate::diagnostic::{Advised, LowerError};
use crate::specialize::{Body, Clause, Definition, Expr, ExprKind, FunctionKey, Program, Type};

/// Refuse the first function value held anywhere but a call's argument.
pub(crate) fn check(program: &Program, package: &[ModuleId]) -> Result<(), LowerError> {
    for function in &program.functions {
        let Definition::Body(clauses) = &function.definition else {
            continue;
        };
        for Clause { guard, body, .. } in clauses {
            let checked = guard
                .iter()
                .try_for_each(|guard| value(guard, false))
                .and_then(|()| self::body(body));
            if let Err(error) = checked {
                return Err(blamed(program, package, &function.key, error));
            }
        }
    }
    Ok(())
}

/// A refusal in `refused`, placed at the first call written in `package`
/// on the way to it where it is outside the package, since that call
/// handed on the function; where it would be held is shown beside it.
fn blamed(
    program: &Program,
    package: &[ModuleId],
    refused: &FunctionKey,
    error: LowerError,
) -> LowerError {
    let Some(held) = error.at else {
        return error;
    };
    if package.contains(&held.0) {
        return error;
    }
    let callers = callers(program);
    let mut seen = HashSet::from([refused]);
    let mut waiting = VecDeque::from([refused]);
    while let Some(callee) = waiting.pop_front() {
        for &(caller, call) in callers.get(callee).into_iter().flatten() {
            if package.contains(&call.module) {
                let mut blamed = located(call, &error.message)
                    .label("this call hands on a function that would be held");
                blamed.advice.notes = error.advice.notes;
                blamed.secondary.push((held, "held here".to_owned()));
                return blamed;
            }
            if seen.insert(caller) {
                waiting.push_back(caller);
            }
        }
    }
    error
}

/// Every call naming a definition, by the definition it names: the caller
/// and the call.
fn callers(program: &Program) -> HashMap<&FunctionKey, Vec<(&FunctionKey, &Expr)>> {
    let mut callers: HashMap<_, Vec<_>> = HashMap::new();
    for function in &program.functions {
        let Definition::Body(clauses) = &function.definition else {
            continue;
        };
        for Clause { guard, body, .. } in clauses {
            let expressions = guard
                .iter()
                .chain(body.bindings.iter().map(|binding| &binding.value))
                .chain([&body.result]);
            for expression in expressions {
                calls(expression, &mut |callee, call| {
                    callers
                        .entry(callee)
                        .or_default()
                        .push((&function.key, call));
                });
            }
        }
    }
    callers
}

/// Each call in `expression` naming a definition, with what it names.
fn calls<'a>(expression: &'a Expr, found: &mut impl FnMut(&'a FunctionKey, &'a Expr)) {
    let inner: Vec<&Expr> = match &expression.kind {
        ExprKind::Local(_)
        | ExprKind::Function(_)
        | ExprKind::ConstructorFunction(_)
        | ExprKind::Natural(_)
        | ExprKind::Bytes(_) => Vec::new(),
        ExprKind::Construct(_, fields) | ExprKind::Tuple(fields) => fields.iter().collect(),
        ExprKind::Record(fields) => fields.iter().map(|(_, field)| field).collect(),
        ExprKind::Update(base, fields) => std::iter::once(&**base)
            .chain(fields.iter().map(|(_, field)| field))
            .collect(),
        ExprKind::Project(inner, _)
        | ExprKind::Lambda(_, _, inner)
        | ExprKind::Widen(inner)
        | ExprKind::Try(inner) => vec![&**inner],
        ExprKind::If(condition, yes, no) => vec![&**condition, &**yes, &**no],
        ExprKind::Is(value, rows) => std::iter::once(&**value)
            .chain(rows.iter().filter_map(|(_, guard)| guard.as_ref()))
            .collect(),
        ExprKind::DirectCall(callee, arguments) => {
            found(callee, expression);
            arguments.iter().collect()
        }
        ExprKind::Invoke(head, arguments) => std::iter::once(&**head).chain(arguments).collect(),
        ExprKind::Block(body) => body
            .bindings
            .iter()
            .map(|binding| &binding.value)
            .chain([&body.result])
            .collect(),
    };
    for expression in inner {
        calls(expression, found);
    }
}

fn body(body: &Body) -> Result<(), LowerError> {
    for binding in &body.bindings {
        value(&binding.value, false)?;
    }
    value(&body.result, false)
}

/// Check `expression`, which is a call's argument or head when `passed`.
fn value(expression: &Expr, passed: bool) -> Result<(), LowerError> {
    placed(expression, passed)?;
    match &expression.kind {
        ExprKind::Local(_)
        | ExprKind::Function(_)
        | ExprKind::ConstructorFunction(_)
        | ExprKind::Natural(_)
        | ExprKind::Bytes(_) => Ok(()),
        ExprKind::Construct(_, fields) => fields.iter().try_for_each(|field| value(field, false)),
        ExprKind::Record(fields) => fields.iter().try_for_each(|(_, field)| value(field, false)),
        ExprKind::Update(base, fields) => {
            value(base, false)?;
            fields.iter().try_for_each(|(_, field)| value(field, false))
        }
        ExprKind::Tuple(members) => members.iter().try_for_each(|member| value(member, false)),
        ExprKind::Project(receiver, _) => value(receiver, false),
        // A block answers a value: a function stands in none of its lines.
        ExprKind::Block(inner) => body(inner),
        ExprKind::DirectCall(_, arguments) => arguments
            .iter()
            .try_for_each(|argument| value(argument, true)),
        ExprKind::Invoke(head, arguments) => {
            value(head, true)?;
            arguments
                .iter()
                .try_for_each(|argument| value(argument, true))
        }
        ExprKind::Lambda(_, _, result) => value(result, false),
        ExprKind::Widen(inner) => value(inner, passed),
        ExprKind::Try(inner) => value(inner, false),
        ExprKind::Is(tested, rows) => {
            value(tested, false)?;
            rows.iter()
                .filter_map(|(_, guard)| guard.as_ref())
                .try_for_each(|guard| value(guard, false))
        }
        ExprKind::If(condition, yes, no) => {
            value(condition, false)?;
            value(yes, false)?;
            value(no, false)
        }
    }
}

/// A function, which may only go straight into a call, and never one with
/// no parameters, which is a value.
fn placed(expression: &Expr, passed: bool) -> Result<(), LowerError> {
    let Type::Function(signature) = &expression.ty else {
        return Ok(());
    };
    if signature.parameters.is_empty() {
        return Err(located(
            expression,
            "a definition with no parameters is a value, reached by its name",
        ));
    }
    if !passed {
        return Err(located(
            expression,
            "a function may only be passed straight into a call",
        )
        .note("a function cannot be bound, answered, or stored"));
    }
    Ok(())
}

fn located(expression: &Expr, message: &str) -> LowerError {
    LowerError::new(message, Some((expression.module, expression.span)))
}
