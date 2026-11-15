//! Float operations, recognized by their code.
//!
//! A float is a pattern wrapped in one-field products down to a natural,
//! and an operation on one is a definition walking that pattern bit by bit.
//! No equation says a walk like that rounds as IEEE 754 does, so Barb does
//! not try to prove it: it knows the standard's own routines by their
//! [`fingerprint`]s, written out ahead of time from the standard and checked
//! against the host's arithmetic. A definition whose code is one of them
//! is that operation; the frontend says nothing about it.

use num_bigint::BigUint;

use crate::float::Float;

use super::budget::Budget;
use super::constant::{ConstantView, Held};
use super::evaluate::{CannotFold, Evaluation};
use super::fingerprint::fingerprint;
use super::program::single_field;
use super::{CtorId, FnId, Program, TypeId, TypeShape, type_shape};

mod known;

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

/// Record, on each definition whose code is a reference float routine,
/// the IEEE 754 operation it computes.
///
/// A candidate takes one or two values of the type it answers, a natural in
/// one or more one-field wrappers. Its [`fingerprint`] -- its code and all
/// the code it reaches, as canonicalizing left it -- is looked up among the
/// standard's own routines. A match is that routine, so it computes that
/// operation exactly as the routine does, and nothing the frontend says is
/// trusted. A definition written any other way is not recognized and
/// answers by its body.
///
/// The fact stays on the definition from here on. A recognized definition
/// is neither rewritten nor inlined, and what its helpers become under
/// rewriting still means what they meant, so the fact still holds where a
/// later fingerprint would differ.
pub(super) fn recognise(program: &mut Program) {
    if program.floats_walked() || known::KNOWN.is_empty() {
        return;
    }
    let found: Vec<_> = (0..program.functions().len())
        .map(FnId::at)
        .filter(|&id| candidate(program, id))
        .filter_map(|id| {
            let print = fingerprint(program, id)?;
            let &(_, float) = known::KNOWN.iter().find(|(known, _)| *known == print)?;
            (float.operation.arity() == program.params(id).len()).then_some((id, float))
        })
        .collect();
    for (id, float) in found {
        program.recognise_float(id, float);
    }
}

/// Whether `id` has the shape of a float operation: a body, taking one or
/// two of the type it answers, which is a natural in one-field wrappers.
fn candidate(program: &Program, id: FnId) -> bool {
    let function = program.function(id);
    let params = program.params(id);
    function.body().is_some()
        && (1..=2).contains(&params.len())
        && params.iter().all(|&ty| ty == function.result)
        && wrapped(program, function.result).is_some_and(|(wrappers, _)| !wrappers.is_empty())
}

/// A recognized float call's answer, from its operands' patterns; nothing where an
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
