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
use crate::context::Context;
use crate::diagnostic::{Advised, Diagnostic, Refusal};
use crate::specialize::{Clause, Definition, Expr, ExprKind, FunctionKey, Program, Type};

/// Refuse the first function value held anywhere but a call's argument.
pub(crate) fn check(program: &Program, cx: &Context) -> Result<(), Diagnostic> {
    first_held(program, &cx.package).map_err(|refusal| cx.told(refusal))
}

fn first_held(program: &Program, package: &[ModuleId]) -> Result<(), Refusal> {
    for function in &program.functions {
        let Definition::Body(clauses) = &function.definition else {
            continue;
        };
        for clause in clauses {
            if let Err(error) = clause
                .exprs()
                .try_for_each(|expression| value(expression, false))
            {
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
    error: Refusal,
) -> Refusal {
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
        for expression in clauses.iter().flat_map(Clause::exprs) {
            expression.for_each_within(&mut |call| {
                if let ExprKind::DirectCall(callee, _) = &call.kind {
                    callers
                        .entry(callee)
                        .or_default()
                        .push((&function.key, call));
                }
            });
        }
    }
    callers
}

/// Check `expression`, which is a call's argument or head when `passed`.
/// A block answers a value: a function stands in none of its lines.
fn value(expression: &Expr, passed: bool) -> Result<(), Refusal> {
    placed(expression, passed)?;
    match &expression.kind {
        ExprKind::DirectCall(..) | ExprKind::Invoke(..) => {
            expression.try_for_each_child(|inner| value(inner, true))
        }
        ExprKind::Widen(inner) => value(inner, passed),
        _ => expression.try_for_each_child(|inner| value(inner, false)),
    }
}

/// A function, which may only go straight into a call, and never one with
/// no parameters, which is a value.
fn placed(expression: &Expr, passed: bool) -> Result<(), Refusal> {
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

fn located(expression: &Expr, message: &str) -> Refusal {
    Refusal::at(expression.module, expression.span, message)
}
