//! Claimed operations: what [`Program::claim`] says a definition computes.
//!
//! A claim is not a proof, and nothing here tries to make it one. What is
//! checked is its shape: a float is a pattern wrapped in one-field products
//! down to a natural, the definition takes and answers the same such type,
//! as many as the operation takes, and has a body that answers where
//! nothing faster does.

use num_bigint::BigUint;

use crate::float::Float;

use super::budget::Budget;
use super::constant::{ConstantView, Held};
use super::evaluate::{CannotFold, Evaluation};
use super::program::single_field;
use super::{CtorId, FnId, Program, TypeId, TypeShape, type_shape};

/// The constructors a pattern of `ty` is wrapped in, outermost first, and
/// the natural inside them; nothing where `ty` is not a wrapped natural.
pub(super) fn wrapped(program: &Program, mut ty: TypeId) -> Option<(Vec<CtorId>, TypeId)> {
    let mut wrappers = Vec::new();
    loop {
        if matches!(type_shape(program, ty), TypeShape::Natural { .. }) {
            return Some((wrappers, ty));
        }
        let (constructor, field) = single_field(program, ty)?;
        wrappers.push(constructor);
        ty = field;
    }
}

/// Whether `id`'s claim, if it has one, has the shape of what it claims.
pub(super) fn check(program: &Program, id: FnId) -> Result<(), String> {
    let function = program.function(id);
    let Some(float) = function.float else {
        return Ok(());
    };
    let name = program.name(function.name);
    let refuse = |why: &str| Err(format!("`{name}` is claimed to be {float}, but {why}"));
    if function.body().is_none() {
        return refuse("it has no body to answer where nothing else does");
    }
    let params = program.params(id);
    if params.len() != float.operation.arity() {
        return refuse(&format!(
            "it takes {} rather than {}",
            params.len(),
            float.operation.arity()
        ));
    }
    if params.iter().any(|&ty| ty != function.result) {
        return refuse("it does not take the type it answers");
    }
    if wrapped(program, function.result).is_none() {
        return refuse("what it answers is not a natural in one-field wrappers");
    }
    Ok(())
}

/// A claimed call's answer, from its operands' patterns; nothing where an
/// operand is no pattern of the format, which the body then answers.
pub(super) fn answer(
    program: &Program,
    float: Float,
    result: TypeId,
    fields: &[Held],
    budget: &mut Budget,
) -> Option<Evaluation> {
    let mut patterns = Vec::with_capacity(fields.len());
    for field in fields {
        let mut held = field.clone();
        let natural = loop {
            match held.as_constant(program.type_info()).view() {
                ConstantView::Natural(natural) => break natural.try_u64().ok()?,
                ConstantView::Constructor(_) => {
                    let parts = held.as_constant(program.type_info()).parts(budget);
                    let (_, mut inner) = match parts {
                        Ok(parts) => parts,
                        Err(limit) => return Some(Err(limit.into())),
                    };
                    held = inner.pop()?;
                }
                ConstantView::Spine(_) => return None,
            }
        };
        if natural > float.format.greatest() {
            return None;
        }
        patterns.push(natural);
    }
    let (wrappers, natural) = wrapped(program, result)?;
    let mut answer = Held::number(
        program.type_info(),
        natural,
        &BigUint::from(float.calculate(&patterns)),
    );
    for &constructor in wrappers.iter().rev() {
        answer = match Held::build(program.type_info(), constructor, &[answer], budget) {
            Ok(answer) => answer,
            Err(super::constant::ConstructionError::Limit(limit)) => {
                return Some(Err(CannotFold::from(limit)));
            }
            Err(error) => panic!("ill-typed float answer: {error}"),
        };
    }
    Some(Ok(answer))
}
