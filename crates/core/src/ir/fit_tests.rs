//! Packing what crosses a boundary preserves what a program answers.
use num_bigint::BigUint;

use super::evaluate::{self, RejectHost};
use super::*;
use crate::programs::abi::{self, Transfer};

fn answer(program: &Program) -> Vec<BigUint> {
    validate(program).expect("a valid program");
    evaluate::evaluate(
        program,
        program.entry(),
        &[],
        evaluate::Config::default(),
        &mut RejectHost,
    )
    .expect("an evaluation")
    .returned()
    .expect("a returning program")
    .to_vec()
}

/// Every boundary within the budget, which is what a target's limits check.
fn within(program: &Program, params: usize, results: usize, transfers: usize) -> bool {
    let entry = program.entry();
    program.functions.iter_enumerated().all(|(id, function)| {
        id == entry
            || (function.params.len() <= params && function.returns.classes().len() <= results)
    }) && program
        .ops
        .iter()
        .zip(&program.results)
        .all(|(op, answered)| match *op {
            Op::If { .. } => answered.len() <= transfers,
            Op::Loop { initial, .. } => initial.len() <= transfers && answered.len() <= transfers,
            _ => true,
        })
}

fn programs() -> Vec<Program> {
    let mut held = vec![
        abi::function(7, 3),
        abi::function(5, 2),
        abi::function(1, 1),
        abi::function(0, 0),
    ];
    for kind in [Transfer::If, Transfer::LoopState, Transfer::LoopResults] {
        held.push(abi::region(kind, 3));
    }
    held
}

#[test]
fn packing_to_any_budget_answers_what_the_program_did() {
    for original in programs() {
        let expected = answer(&original);
        for (params, results, transfers) in [(1, 1, 1), (2, 1, 2), (4, 1, 2), (6, 2, 3)] {
            let fitted = fit(&original, Budget::new(params, results, transfers));
            assert!(within(&fitted, params, results, transfers));
            assert_eq!(answer(&fitted), expected, "{params}/{results}/{transfers}");
        }
    }
}

#[test]
fn a_program_within_its_budget_is_unchanged() {
    for original in programs() {
        let fitted = fit(&original, Budget::UNLIMITED);
        assert_eq!(fitted.ops, original.ops);
        assert_eq!(fitted.signature, original.signature);
    }
}

#[test]
fn a_packed_run_keeps_the_leading_places_and_the_first_packed_name() {
    let original = abi::function(7, 3);
    let fitted = fit(&original, Budget::new(4, 2, 2));
    let wide = FunctionId::at(1);
    assert_eq!(
        fitted.signature(fitted.function(wide).params),
        [Class::Word, Class::Word, Class::Word, Class::Cell]
    );
    assert_eq!(
        fitted.signature(fitted.function(wide).returns.classes()),
        [Class::Word, Class::Cell]
    );
    assert_eq!(
        fitted.parameter_names(wide).collect::<Vec<_>>(),
        ["v0", "v1", "v2", "v3"]
    );
    // The entry is bound by the target and keeps its own signature.
    assert_eq!(
        fitted.signature(fitted.function(fitted.entry()).returns.classes()),
        [Class::Word]
    );
}
