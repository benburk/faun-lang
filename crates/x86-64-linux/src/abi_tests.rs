use faun_core::ir::validate;
use faun_core::programs::abi::{self, Transfer};
use faun_core::targets::Target;

use crate::X86_64Linux;

#[test]
fn rejects_valid_ir_outside_the_function_calling_convention() {
    for (params, returns, diagnostic) in [(7, 1, "7 parameters"), (0, 2, "2 results")] {
        let program = abi::function(params, returns);
        validate(&program).unwrap();
        let error = X86_64Linux.accepts(&program).unwrap_err();
        assert!(error.contains("x86-64-linux function `wide`"), "{error}");
        assert!(error.contains(diagnostic), "{error}");
    }
}

#[test]
fn cannot_silently_drop_a_second_pointer_result() {
    let program = abi::pointer_pair();
    validate(&program).unwrap();
    let error = X86_64Linux.accepts(&program).unwrap_err();
    assert!(error.contains("function `pair` has 2 results"), "{error}");
}

#[test]
fn accepts_supported_function_arities_and_multivalue_regions() {
    for (params, returns) in [(6, 1), (0, 0)] {
        let program = abi::function(params, returns);
        validate(&program).unwrap();
        X86_64Linux.accepts(&program).unwrap();
        X86_64Linux.emit(&program);
    }
    for kind in [Transfer::If, Transfer::LoopState, Transfer::LoopResults] {
        let program = abi::region(kind, 3);
        validate(&program).unwrap();
        X86_64Linux.accepts(&program).unwrap();
        X86_64Linux.emit(&program);
    }
}
