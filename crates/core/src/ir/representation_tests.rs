use super::*;
use crate::{barb, platform::Routines};

const NAT: &str = include_str!("../../../../crates/simple/standard/nat.fn");
const BYTE: &str = include_str!("../../../../crates/simple/standard/u8.fn");
const INT: &str = include_str!("../../../../crates/simple/standard/int.fn");

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
        let uncleaned = crate::read_with_options(
            &text,
            &routines,
            &barb::OptimizeOptions {
                cleanup: false,
                ..barb::OptimizeOptions::default()
            },
        )
        .unwrap();
        validate(&uncleaned).unwrap();
    }
}

#[test]
fn default_pipeline_accepts_runtime_product_programs() {
    for main in [
        "main!(h) -> n = argc!(h) byte = u8_from_nat_wrapping(n) converted = u8_to_nat(byte) exit!(h Zero)",
        "main!(h) -> n = argc!(h) signed = int_from_nat(n) magnitude = int_abs(signed) exit!(h Zero)",
    ] {
        let machine = crate::read(&library(main), &Routines::builtin().with_word(64)).unwrap();
        validate(&machine).unwrap();
    }
}

/// A byte is a product of eight flags, held flat as eight words; a signed
/// number is a sum carrying a payload, held as a cell. Neither unused
/// binding is erased by lowering.
#[test]
fn runtime_products_and_signed_sums_lower_without_erasing_unused_bindings() {
    for (text, cells) in [
        (
            "main!(h) -> n = argc!(h) byte = u8_from_nat_wrapping(n) converted = u8_to_nat(byte) exit!(h Zero)",
            false,
        ),
        (
            "main!(h) -> n = argc!(h) signed = int_from_nat(n) magnitude = int_abs(signed) exit!(h Zero)",
            true,
        ),
        ("main!(h) -> byte = u8_zero() exit!(h Zero)", false),
    ] {
        let machine = lower_program(&parse(&library(text))).unwrap();
        validate(&machine).unwrap();
        assert_eq!(
            machine.ops.iter().any(|op| matches!(op, Op::Cell { .. })),
            cells,
            "{}",
            machine.render()
        );
        assert!(
            bodies(&machine) > 1,
            "the library calls are lowered, not erased"
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

/// A wrapper around a product is held as that product, so matching one binds
/// the product itself rather than taking a step into it. Both are held flat,
/// so nothing is built and nothing is read back.
#[test]
fn a_wrapper_around_a_product_stays_transparent_when_matched() {
    let text = library(
        "type Pair MkPair(Nat Nat)
         type Boxed MkBoxed(Pair)
         unbox(MkBoxed(p)) -> p
         first(MkPair(a b)) -> a
         main!(h) ->
           n = argc!(h)
           held = MkBoxed(MkPair(n Zero))
           inner = unbox(held)
           exit!(h mod(first(inner) Succ(Succ(Zero))))",
    );
    let machine = lower_program(&parse(&text)).unwrap();
    validate(&machine).unwrap();
    let rendered = machine.render();
    assert!(
        !machine
            .ops
            .iter()
            .any(|op| matches!(op, Op::Cell { .. } | Op::CellField { .. })),
        "{rendered}"
    );
    // The wrapper and the product it holds are the same two values.
    let unbox = machine
        .functions()
        .iter()
        .find(|function| machine.name(function.name) == "unbox")
        .expect("unbox is lowered");
    assert_eq!(
        machine.signature(unbox.params),
        machine.signature(unbox.returns.classes())
    );
    assert_eq!(machine.signature(unbox.params).len(), 2, "{rendered}");
}

/// A cell's fields are held at the class the cell says, which is the class a
/// projection reads them back at. Storing a value at whatever width it was
/// worked out as would let a projection read a count as an address.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture declares its types, builds its values, and checks facts and evaluation"
)]
fn cell_fields_are_held_at_the_class_their_projection_reads() {
    let text = library(
        "type Pair NoPair MkPair(Nat Nat)
         first(NoPair) -> Zero
         first(MkPair(a b)) -> a
         main!(h) ->
           n = argc!(h)
           held = MkPair(n Zero)
           exit!(h mod(first(held) Succ(Succ(Zero))))",
    );
    let machine = lower_program(&parse(&text)).unwrap();
    validate(&machine).unwrap();
    let rendered = machine.render();
    let mut built = Vec::new();
    let mut read = Vec::new();
    for (op, results) in machine
        .functions()
        .iter()
        .filter_map(Function::body)
        .flat_map(|body| machine.walk_within(body))
    {
        match *op {
            Op::Cell { fields, .. } => built.extend(
                machine
                    .values(fields)
                    .iter()
                    .map(|&field| machine.class(field)),
            ),
            Op::CellField { index, .. } => read.push((index, machine.class(results[0]))),
            _ => {}
        }
    }
    // The count is held as wide as a count can be, and the second field
    // only ever holds nought: each field is as wide as what is built there.
    assert_eq!(
        built,
        [
            Class::Held(barb::Bounds {
                low: 0,
                high: Some(u64::MAX)
            }),
            Class::fixed(0)
        ],
        "{rendered}"
    );
    assert!(!read.is_empty(), "{rendered}");
    for (index, class) in read {
        assert_eq!(class, built[usize::try_from(index).unwrap()], "{rendered}");
    }
}
