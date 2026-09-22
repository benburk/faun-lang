use super::ast::{BinaryOp, ExprKind, Item, Pattern, Type};
use super::parse;

#[test]
fn parses_the_first_order_ori_slice() {
    let source = r"
        Nat : [Zero Succ(Nat)]

        add : Nat Nat -> Nat
        add(0 y) -> y
        add(Succ(n) y) ->
          next = n + y
          Succ(next)
    ";
    let module = parse(source).unwrap();
    assert_eq!(module.items.len(), 4);

    let Item::Data(nat) = &module.items[0] else {
        panic!("a data declaration")
    };
    assert_eq!(nat.name.text(source), "Nat");
    assert_eq!(nat.constructors[1].name.text(source), "Succ");
    let Type::Named { name, .. } = &nat.constructors[1].fields[0];
    assert_eq!(name.text(source), "Nat");

    let Item::Signature(add) = &module.items[1] else {
        panic!("a signature")
    };
    assert_eq!(add.name.text(source), "add");
    assert_eq!(add.parameters.len(), 2);

    let Item::Clause(recursive) = &module.items[3] else {
        panic!("a clause")
    };
    assert!(matches!(recursive.patterns[0], Pattern::Constructor { .. }));
    assert_eq!(recursive.body.bindings.len(), 1);
    assert!(matches!(
        recursive.body.bindings[0].value.kind,
        ExprKind::Binary(BinaryOp::Add, ..)
    ));
}

#[test]
fn parses_effect_names_and_method_chains() {
    let source = "main!(host) -> host.args!().length() + 1";
    let module = parse(source).unwrap();
    let Item::Clause(clause) = &module.items[0] else {
        panic!("a clause")
    };
    assert_eq!(clause.name.text(source), "main!");
    assert!(matches!(
        clause.body.result.kind,
        ExprKind::Binary(BinaryOp::Add, ..)
    ));
}

#[test]
fn adjacency_distinguishes_calls_from_peers() {
    parse("id(x) -> f(x)").unwrap();
    let error = parse("id(x) -> f (x)").unwrap_err();
    assert_eq!(error.line, 1);
    assert!(error.message.contains("end of the file"));
}

#[test]
fn comments_and_newlines_are_separators() {
    parse("Pair(a b) : [Pair(a # first field\n b)]\nfirst(Pair(a _)) -> a").unwrap();
}

#[test]
fn constructor_shaped_bindings_and_results_stay_distinct() {
    let source = "unwrap(value) -> Some(inner) = value Some(Some(inner))";
    let module = parse(source).unwrap();
    let Item::Clause(clause) = &module.items[0] else {
        panic!("a clause")
    };
    assert!(matches!(
        clause.body.bindings[0].pattern,
        Pattern::Constructor { .. }
    ));
    assert!(matches!(clause.body.result.kind, ExprKind::Call(..)));
}

#[test]
fn commas_and_forms_outside_the_subset_are_rejected() {
    let comma = parse("f(x, y) -> x").unwrap_err();
    assert!(comma.message.contains("invalid token `,`"));

    let method_block = parse("Nat : [Zero].(zero() -> Zero)").unwrap_err();
    assert!(method_block.offset > 0);

    let field_projection = parse("get(record) -> record.field").unwrap_err();
    assert!(field_projection.offset > 0);
}

#[test]
fn errors_report_the_source_position() {
    let error = parse("id(x) -> x\nnext(x) -> @").unwrap_err();
    assert_eq!((error.line, error.column), (2, 12));
    assert!(error.message.contains("invalid token `@`"));
}
