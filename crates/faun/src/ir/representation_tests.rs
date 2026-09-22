use super::*;
use crate::{barb, platform::Routines};

const NAT: &str = include_str!("../../../../standard/nat.fn");
const BYTE: &str = include_str!("../../../../standard/u8.fn");
const INT: &str = include_str!("../../../../standard/int.fn");

fn bodies(program: &Program) -> usize {
    program
        .functions()
        .iter()
        .filter_map(Function::body)
        .count()
}

fn externals(program: &Program) -> usize {
    program
        .functions()
        .iter()
        .filter_map(Function::external)
        .count()
}

fn library(main: &str) -> String {
    format!("{NAT}\n{BYTE}\n{INT}\n{main}")
}

fn parse(text: &str) -> barb::Program {
    crate::simple::parse(text, &Routines::builtin().with_word(64)).unwrap()
}

fn lower_program(source: &barb::Program) -> Result<Program, String> {
    lower(
        source,
        &barb::analyze(source),
        &Routines::builtin().with_word(64),
    )
}

#[test]
fn unused_library_types_and_functions_do_not_need_runtime_representations() {
    let text = library(
        "main!(h) ->
           n = argc!(h)
           exit!(h mod(n Succ(Succ(Zero))))",
    );
    for machine in [
        lower_program(&parse(&text)).unwrap(),
        crate::read(&text, &Routines::builtin().with_word(64)).unwrap(),
    ] {
        validate(&machine).unwrap();
        assert_eq!(bodies(&machine), 1, "only main is emitted");
        assert_eq!(externals(&machine), 2, "argc and exit are retained");
    }
}

#[test]
fn folded_library_calls_leave_no_runtime_representation_demand() {
    let text = library(
        "byte_status() -> u8_to_nat(u8_sub_wrapping(u8_zero() u8_from_nat_wrapping(Succ(Zero))))
         signed_status() -> int_abs(int_sub(Pos(Zero) Pos(Succ(Zero))))
         main!(h) -> exit!(h add(byte_status() signed_status()))",
    );
    let mut source = parse(&text);
    barb::fold(&mut source);
    // The old function bodies and library types remain in the arenas, but
    // their callers now hold naturals, not products or signed sums.
    let machine = lower_program(&source).unwrap();
    assert_eq!(bodies(&machine), 1);
    assert_eq!(externals(&machine), 1);
}

#[test]
fn default_pipeline_removes_folded_library_temporaries() {
    for (main, expected) in [
        (
            "main!(h) -> exit!(h u8_to_nat(u8_sub_wrapping(u8_zero() u8_from_nat_wrapping(Succ(Zero)))))",
            255,
        ),
        (
            "main!(h) -> a = Pos(Zero) b = Pos(Succ(Zero)) difference = int_sub(a b) exit!(h int_abs(difference))",
            1,
        ),
        (
            "main!(h) -> a = u8_zero() b = u8_from_nat_wrapping(Succ(Zero)) byte = u8_sub_wrapping(a b) n = u8_to_nat(byte) signed = int_sub(Pos(Zero) Pos(Succ(Zero))) magnitude = int_abs(signed) exit!(h add(n magnitude))",
            256,
        ),
    ] {
        let text = library(main);
        let routines = Routines::builtin().with_word(64);
        let machine = crate::read(&text, &routines).unwrap();
        validate(&machine).unwrap();
        assert_eq!(bodies(&machine), 1);
        assert_eq!(externals(&machine), 1, "only exit remains");
        assert!(
            machine
                .every(machine.function(machine.entry()).body().unwrap())
                .any(|op| matches!(op, Op::Constant { value, .. } if *value == expected))
        );
        assert!(
            crate::read_with_options(
                &text,
                &routines,
                &barb::OptimizeOptions {
                    cleanup: false,
                    ..barb::OptimizeOptions::default()
                }
            )
            .is_err(),
            "without cleanup, dead products still demand storage"
        );
    }
}

#[test]
fn default_pipeline_still_rejects_runtime_products() {
    for main in [
        "main!(h) -> n = argc!(h) byte = u8_from_nat_wrapping(n) exit!(h u8_to_nat(byte))",
        "main!(h) -> n = argc!(h) signed = int_from_nat(n) exit!(h int_abs(signed))",
    ] {
        let error = crate::read(&library(main), &Routines::builtin().with_word(64)).unwrap_err();
        assert!(error.contains("has no representation"), "{error}");
    }
}

#[test]
fn runtime_products_and_signed_sums_are_still_rejected() {
    for (name, text) in [
        (
            "U8",
            "main!(h) -> n = argc!(h) byte = u8_from_nat_wrapping(n) exit!(h u8_to_nat(byte))",
        ),
        (
            "Int",
            "main!(h) -> n = argc!(h) signed = int_from_nat(n) exit!(h int_abs(signed))",
        ),
        ("U8", "main!(h) -> byte = u8_zero() exit!(h Zero)"),
    ] {
        // Even an unused binding still demands storage until an optimizer
        // actually removes it; lowering must never pretend it is erased.
        let error = lower_program(&parse(&library(text))).unwrap_err();
        assert!(
            error.contains(&format!("`{name}` has no representation")),
            "{error}"
        );
    }
}

#[test]
fn unsupported_types_in_impossible_arms_do_not_demand_storage_or_functions() {
    for (good, bad, argument) in [
        ("Zero", "Succ(n)", "Zero"),
        ("Succ(n)", "Zero", "Succ(Zero)"),
        ("True", "False", "True"),
    ] {
        let text = library(&format!(
            "select!(h {good}) -> exit!(h Zero)
             select!(h {bad}) -> byte = u8_zero() exit!(h u8_to_nat(byte))
             main!(h) -> select!(h {argument})"
        ));
        // No folding or inlining: the lowering's own reachability must agree
        // between function discovery, type demand, and branch emission.
        let machine = lower_program(&parse(&text)).unwrap();
        assert_eq!(bodies(&machine), 2, "main and select only");
        assert_eq!(externals(&machine), 1);
    }
}

#[test]
fn recognized_definition_bodies_do_not_demand_runtime_representations() {
    let text = library("main!(h) -> n = argc!(h) exit!(h add(n Zero))")
        .replace("add(a Zero) -> a", "add(a Zero) -> ignored = Pos(a) a");
    let source = parse(&text);
    let facts = barb::analyze(&source);
    let add = barb::FnId::at(
        source
            .functions()
            .iter()
            .position(|f| source.name(f.name) == "add")
            .unwrap(),
    );
    assert_eq!(facts.operation(add), Some(barb::Operation::Add));
    let machine = lower(&source, &facts, &Routines::builtin().with_word(64)).unwrap();
    assert_eq!(bodies(&machine), 1, "add becomes an instruction");
}

#[test]
fn unsupported_values_after_nonreturning_bindings_are_not_lowered() {
    for exit in ["exit!(h Zero)", "stop!(h n)"] {
        let text = library(&format!(
            "stop!(h Zero) -> exit!(h Zero)
             stop!(h Succ(n)) -> exit!(h Zero)
             main!(h) ->
               count = argc!(h)
               n = add(count Zero)
               never = {exit}
               byte = u8_zero()
               exit!(h u8_to_nat(byte))"
        ));
        for normalized in [false, true] {
            let mut source = parse(&text);
            if normalized {
                // The second case becomes a match whose every arm leaves.
                barb::normalize_with_limits(&mut source, barb::InlineLimits::default());
            }
            lower_program(&source).unwrap();
        }
    }
}

#[test]
fn detached_arena_expressions_do_not_demand_a_representation() {
    let mut source = parse(&library(
        "main!(h) -> byte = u8_zero() exit!(h u8_to_nat(byte))",
    ));
    let exit = barb::FnId::at(
        source
            .functions()
            .iter()
            .position(|f| source.name(f.name) == "exit!")
            .unwrap(),
    );
    let nat = source.params(exit)[1];
    let zero = source.intern_number(nat, 0).unwrap();
    source.define(source.entry().unwrap(), |b, args| {
        let zero = b.known(zero);
        b.call(exit, &[args[0], zero])
    });
    let machine = lower_program(&source).unwrap();
    assert_eq!(bodies(&machine), 1);
    assert_eq!(externals(&machine), 1);
}
