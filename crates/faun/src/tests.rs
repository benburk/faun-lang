use super::ast::{Body, ExprKind, Item, UnaryOp};
use super::parse;

#[test]
fn errors_report_the_source_position() {
    let error = parse("id(x) -> x\nnext(x) -> @").unwrap_err();
    assert_eq!((error.line, error.column), (2, 12));
    assert!(error.message.contains("invalid token `@`"));
}

#[test]
fn an_unfinished_type_lists_what_could_come_next() {
    let error = parse("main! : Host -> \n").unwrap_err();
    assert_eq!(
        error.message,
        "expected one of `(`, `[`, `{`, a name, a type name before the end of the file"
    );
}

/// The one body of `source`'s one clause.
fn body(source: &str) -> Body {
    match parse(source).unwrap().items.pop() {
        Some(Item::Clause(clause)) => clause.body,
        other => panic!("expected a clause, found {other:?}"),
    }
}

#[test]
fn items_and_statements_end_with_their_lines() {
    let error = parse("main! : Host -> [] main!(host) -> host.exit!(0)").unwrap_err();
    assert!(error.message.contains("a new line"), "{}", error.message);
    let error = parse("f(x) ->\n  y = x").unwrap_err();
    assert!(
        error
            .message
            .contains("a line answering the body after its last binding"),
        "{}",
        error.message
    );
}

#[test]
fn a_body_is_its_lines_and_its_last_line_is_its_answer() {
    let lines = body("f(x) ->\n  log!(x)\n  y = x\n  -y\n");
    assert_eq!(lines.bindings.len(), 2);
    assert!(lines.bindings[0].discarded && !lines.bindings[1].discarded);
    assert!(matches!(
        lines.result.kind,
        ExprKind::Unary(UnaryOp::Negate, _)
    ));
}

#[test]
fn a_line_goes_on_after_an_arrow_or_an_operator_and_into_a_chain() {
    let lines = body("f(x) ->\n  x\n    .g()\n    + 1 *\n    2\n");
    assert!(lines.bindings.is_empty());
    let module = parse(
        "sum : List(a) -> a where\n  a.zero : a\n  a.add : a a -> a\nsum(values) -> values\n",
    )
    .unwrap();
    assert!(matches!(
        &module.items[0],
        Item::Signature(signature) if signature.constraints.len() == 2
    ));
}

#[test]
fn spacing_that_could_mean_two_things_is_refused() {
    let error = parse("f(a b) ->\n  [a -b]\n").unwrap_err();
    assert!(error.message.contains("`(-b)`"), "{}", error.message);
    let error = parse("f(a b) -> a- b\n").unwrap_err();
    assert!(
        error.message.contains("`-` has space on one side only"),
        "{}",
        error.message
    );
    let lines = body("f(a) ->\n  [-4 -5 *a]\n");
    assert!(
        matches!(lines.result.kind, ExprKind::List(ref elements, Some(_)) if elements.len() == 2)
    );
}

#[test]
fn parentheses_nest_without_trying_each_reading_again() {
    let depth = 200;
    let source = format!("f(x) -> {}x{}\n", "(".repeat(depth), ")".repeat(depth));
    assert!(matches!(body(&source).result.kind, ExprKind::Name(_)));
    let types = parse("f : (a b -> c) (a b) (a) -> {x: a *}\n").unwrap();
    assert!(matches!(
        &types.items[0],
        Item::Signature(signature) if signature.parameters.len() == 3
    ));
}
