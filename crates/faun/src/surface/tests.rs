use super::ast::{
    BinaryOp, DataRepresentation, ExprKind, Item, MethodItem, NumeralKind, Pattern, StringPart,
    Type,
};
use super::{Sources, parse, parse_in};

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
    assert_eq!(nat.constructors()[1].name.text(source), "Succ");
    let Type::Named { name, .. } = &nat.constructors()[1].fields[0] else {
        panic!("a named field type")
    };
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
fn commas_and_records_outside_the_subset_are_rejected() {
    let comma = parse("f(x, y) -> x").unwrap_err();
    assert!(comma.message.contains("invalid token `,`"));

    let record = parse("point() -> {x: 1}").unwrap_err();
    assert!(record.offset > 0);
}

#[test]
fn errors_report_the_source_position() {
    let error = parse("id(x) -> x\nnext(x) -> @").unwrap_err();
    assert_eq!((error.line, error.column), (2, 12));
    assert!(error.message.contains("invalid token `@`"));
}

#[test]
fn parses_module_interfaces_methods_guards_and_constraints() {
    let source = r"
        lib {}
        import data.nat {Nat.*}
        exports {Int.*}
        Int : [Pos(Nat) NegSucc(Nat)].(
          of_nat : Nat -> Int
          of_nat(n) -> Pos(n)
          hash_into : Int h -> h where Hasher(h)
          abs(NegSucc(n)) if n > 0 -> n
        )
    ";
    let module = parse(source).unwrap();
    assert!(matches!(module.items[0], Item::Header(_)));
    assert!(matches!(module.items[1], Item::Import(_)));
    assert!(matches!(module.items[2], Item::Exports(_)));
    let Item::Data(int) = &module.items[3] else {
        panic!("Int declaration")
    };
    assert!(matches!(int.representation, DataRepresentation::Sum(_)));
    assert_eq!(int.methods.len(), 4);
    let MethodItem::Signature(hash) = &int.methods[2] else {
        panic!("hash signature")
    };
    assert_eq!(hash.constraints.len(), 1);
    let MethodItem::Clause(abs) = &int.methods[3] else {
        panic!("guarded clause")
    };
    assert!(abs.guard.is_some());
}

#[test]
fn literals_retain_spelling_and_validate_escapes() {
    let source = "values() -> [0xff 'é' \"a\\n${1}\"]";
    let module = parse(source).unwrap();
    let Item::Clause(clause) = &module.items[0] else {
        panic!("clause")
    };
    let ExprKind::List(values, None) = &clause.body.result.kind else {
        panic!("list")
    };
    let ExprKind::Number(hex) = values[0].kind else {
        panic!("hex numeral")
    };
    assert_eq!(hex.text(source), "0xff");
    assert_eq!(hex.radix(source), 16);
    let ExprKind::Number(character) = values[1].kind else {
        panic!("character numeral")
    };
    assert_eq!(character.kind, NumeralKind::Character);
    let ExprKind::String(parts) = &values[2].kind else {
        panic!("string")
    };
    assert!(matches!(parts[0], StringPart::Text(_)));
    assert!(matches!(parts[1], StringPart::Splice(_)));

    let error = parse("bad() -> \"\\q\"").unwrap_err();
    assert!(error.message.contains("unknown escape"));
}

#[test]
fn parsed_module_carries_source_identity_once() {
    let mut sources = Sources::default();
    let source = sources.add("test.ori", "id(x) -> x");
    assert_eq!(parse_in("id(x) -> x", source).unwrap().source, source);
}
