use faun_core::ir::{Class, Program};
use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;

/// Raw acceptance still enforces the native convention; the compilation
/// wrappers fit a program to it first, so none of these is refused.
#[test]
fn compilation_wrappers_fit_programs_to_native_abi_and_transfer_limits() {
    use faun_core::programs::abi;
    for p in [
        abi::function(4, 1),
        abi::function(5, 1),
        abi::function(0, 2),
        abi::pointer_pair(),
        abi::region(abi::Transfer::If, 3),
        abi::region(abi::Transfer::LoopState, 3),
        abi::region(abi::Transfer::LoopResults, 3),
    ] {
        let prepared = Mos6502Sim65.prepare(&p).unwrap();
        Mos6502Sim65.accepts(&prepared).unwrap();
        Mos6502Sim65.compile_machine_ir(&p).unwrap();
    }
}

/// A program using the natural runtime compiles, its data and heap below
/// the half of memory an immediate's address would be in.
#[test]
fn runtime_naturals_compile_below_half_of_memory() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 42);
        let natural = b.convert(Class::Natural, value);
        let result = b.convert(Class::Word, natural);
        b.ret(&[result]);
    });
    Mos6502Sim65.compile_machine_ir(&p).unwrap();
}

/// Data reaching past `$8000` would put the heap where an object's address
/// reads as a number, so a program using naturals is refused there.
#[test]
fn naturals_are_refused_where_the_heap_would_pass_half_of_memory() {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let far = b.data(&vec![1; 0x7000]);
        let at = b.address_of(far);
        let byte = b.load(
            faun_core::ir::Width::Byte,
            at,
            faun_core::ir::Offset::Bytes(0),
        );
        let natural = b.convert(Class::Natural, byte);
        let doubled = b.binary(faun_core::ir::Binary::Add, natural, natural);
        let result = b.convert(Class::Word, doubled);
        b.ret(&[result]);
    });
    let error = Mos6502Sim65.compile_machine_ir(&p).unwrap_err();
    assert!(
        error.contains("below which a natural's objects must lie"),
        "{error}"
    );
}
