use super::ast::{BinaryOp, Body, Clause, ExprKind, Item, Pattern, UnaryOp};
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
            .contains("a body ends with its answer, a line after its last binding"),
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
        "sum : List(a) -> a where\n  a.zero : a\n  a.add : (a, a) -> a\nsum(values) -> values\n",
    )
    .unwrap();
    assert!(matches!(
        &module.items[0],
        Item::Signature(signature) if signature.constraints.len() == 2
    ));
}

#[test]
fn elements_are_parted_by_commas_however_they_are_spaced() {
    let lines = body("f(a, b) ->\n  [a -b, a- b,]\n");
    assert!(matches!(
        lines.result.kind,
        ExprKind::List(ref elements, None) if elements.len() == 2
            && elements.iter().all(|element| matches!(element.kind, ExprKind::Binary(..)))
    ));
    let error = parse("f(a b) -> a\n").unwrap_err();
    assert!(error.message.contains("`,`"), "{}", error.message);
    let error = parse("f(a) -> (a,)\n").unwrap_err();
    assert!(
        error.message.contains("at least two members"),
        "{}",
        error.message
    );
    let lines = body("f(a) ->\n  [-4, -5, *a]\n");
    assert!(
        matches!(lines.result.kind, ExprKind::List(ref elements, Some(_)) if elements.len() == 2)
    );
}

#[test]
fn parentheses_nest_without_trying_each_reading_again() {
    let depth = 200;
    let source = format!("f(x) -> {}x{}\n", "(".repeat(depth), ")".repeat(depth));
    assert!(matches!(body(&source).result.kind, ExprKind::Name(_)));
    let types = parse("f : ((a, b) -> c, (a, b), (a)) -> {x: a, *}\n").unwrap();
    assert!(matches!(
        &types.items[0],
        Item::Signature(signature) if signature.parameters.len() == 3
    ));
}

/// The patterns of `source`'s one clause.
fn patterns(source: &str) -> Vec<Pattern> {
    match parse(source).unwrap().items.pop() {
        Some(Item::Clause(clause)) => clause.patterns,
        other => panic!("expected a clause, found {other:?}"),
    }
}

#[test]
fn a_pattern_is_the_expression_that_builds_what_it_matches() {
    let written = patterns(
        "f(x, _, Some(y), Opt.None, [a, *], [b, *rest], {c, *}, {d, e: 1}, (g, h), 1..9, -2, 'z', \"s\", A | B) -> x\n",
    );
    assert!(matches!(
        written[..],
        [
            Pattern::Bind(_),
            Pattern::Wild(_),
            Pattern::Constructor {
                qualifier: None,
                ..
            },
            Pattern::Constructor {
                qualifier: Some(_),
                ..
            },
            Pattern::List { rest: Some(_), .. },
            Pattern::List { rest: Some(_), .. },
            Pattern::Record { open: true, .. },
            Pattern::Record { open: false, .. },
            Pattern::Tuple { .. },
            Pattern::Range { .. },
            Pattern::Number { negative: true, .. },
            Pattern::Number {
                negative: false,
                ..
            },
            Pattern::String { .. },
            Pattern::Or { .. },
        ]
    ));
    let lines = body("f(xs) ->\n  Some(y) = xs.first()\n  xs.map(|Some(z), _| z)\n");
    assert!(matches!(
        lines.bindings[0].pattern,
        Pattern::Constructor { .. }
    ));
    assert!(matches!(lines.result.kind, ExprKind::Method(..)));
}

#[test]
fn what_is_not_a_pattern_or_only_a_pattern_says_so() {
    for (source, said) in [
        ("f(x + 1) -> x\n", "`x + 1` is not a pattern"),
        ("f(g(x)) -> x\n", "`g(x)` is not a pattern"),
        ("f(x) -> _\n", "`_` stands only in a pattern"),
        ("f(x) -> [x, *]\n", "a list's rest names what follows"),
        ("f(x) -> 1..2\n", "a range stands only in a pattern"),
        ("f(9..0) -> 1\n", "`9..0` is reversed"),
        ("f(-1..-5) -> 1\n", "`-1..-5` is reversed"),
        ("f(1..-1) -> 1\n", "`1..-1` is reversed"),
        ("f(_.._) -> 1\n", "`_.._` bounds nothing"),
        ("f(-(1..3)) -> 1\n", "`-(1..3)` is not a pattern"),
        ("f(x) -> x\nf : Nat -> Nat\nz\n", "belongs to no definition"),
        (
            "F(x) -> x\n",
            "a clause begins with its name and its patterns",
        ),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
}

#[test]
fn every_line_that_cannot_be_read_is_told_at_once() {
    let error =
        parse("f(x) -> x .y\ng(y) -> y\nh(z) -> [z w]\nk(w) -> w)\nm(v) -> v\n").unwrap_err();
    let told: Vec<_> = std::iter::once(&error)
        .chain(&error.also)
        .map(|error| (error.line, error.message.as_str()))
        .collect();
    assert_eq!(told.len(), 3, "{told:?}");
    assert_eq!(told[0].0, 1);
    assert!(told[0].1.contains("no space around it"), "{told:?}");
    assert_eq!(told[1].0, 3);
    assert!(told[1].1.contains("`,`"), "{told:?}");
    assert_eq!(told[2].0, 4);
    assert!(told[2].1.contains("found `)`"), "{told:?}");
}

/// The clauses of `source`, in order.
fn clauses(source: &str) -> Vec<Clause> {
    parse(source)
        .unwrap()
        .items
        .into_iter()
        .filter_map(|item| match item {
            Item::Clause(clause) => Some(clause),
            _ => None,
        })
        .collect()
}

#[test]
fn a_guard_stands_between_a_clause_s_patterns_and_its_arrow() {
    let read = clauses(
        "f(Some(x), y) if x > 1 & y.ok() | !x ->\n  z = x\n  z\nf(_, _) -> 0\ng(x) if\n  x -> x\n",
    );
    let [guarded, fallback, continued] = &read[..] else {
        panic!("three clauses, found {read:?}");
    };
    assert!(matches!(
        guarded.guard.as_ref().map(|guard| &guard.kind),
        Some(ExprKind::Binary(BinaryOp::Or, ..))
    ));
    assert_eq!(guarded.body.bindings.len(), 1);
    assert!(fallback.guard.is_none());
    assert!(matches!(
        continued.guard.as_ref().map(|guard| &guard.kind),
        Some(ExprKind::Name(_))
    ));
}

#[test]
fn a_guard_is_one_expression_and_only_a_clause_has_one() {
    for (source, said) in [
        ("f(x) if -> x\n", "expected an expression, found `->`"),
        ("f(x) if x\n", "expected `->`"),
        ("f(x) if x if y -> x\n", "expected `->`, found `if`"),
        ("f(x) if x = 1 -> x\n", "expected `->`, found `=`"),
        ("f(x) -> x if x\n", "found `if`"),
        ("f : Nat if x -> Nat\n", "found `if`"),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
}

#[test]
fn a_range_s_ends_may_be_negated_or_left_open() {
    let written = patterns("f(_..-1, -3..5, 0.._, -2..-1) -> 1\n");
    let ends: Vec<_> = written
        .iter()
        .map(|pattern| match pattern {
            Pattern::Range { start, end, .. } => (
                start.map(|bound| bound.negative),
                end.map(|bound| bound.negative),
            ),
            other => panic!("a range, found {other:?}"),
        })
        .collect();
    assert_eq!(
        ends,
        [
            (None, Some(true)),
            (Some(true), Some(false)),
            (Some(false), None),
            (Some(true), Some(true)),
        ]
    );
}

#[test]
fn decimal_limits_do_not_depend_on_other_literals_in_the_file() {
    for suffix in ["", "\ntext() -> \"text\"", "\ncharacter() -> 'x'"] {
        for exponent in ["10001", "-10001", "4294967296"] {
            let source = format!("number() -> 1.0e{exponent}{suffix}");
            let error = parse(&source).unwrap_err();
            assert!(error.message.contains("reaches past 10000"), "{error}");
            assert_eq!((error.line, error.column), (1, 13));
        }
    }
    for exponent in ["10000", "-10000"] {
        parse(&format!("number() -> 1.0e{exponent}")).unwrap();
    }
}

#[test]
fn literal_validation_reaches_every_syntactic_position() {
    for source in [
        r#"value() -> "\q""#,
        r#"match("\q") -> 0"#,
        r"match('\q'..'z') -> 0",
        r"match(x) if x == '\q' -> 0",
        "value() ->\n  x = '\\q'\n  x",
        r"value() -> map(|'\q'| 0)",
        r#"value() -> "${'\q'}""#,
        r#"value() -> "${"\q"}""#,
        "T : Nat.(\n  value() -> \"\\q\"\n)",
        r#"expect "\q" == """#,
        r#"package {dep: "\q"}"#,
    ] {
        let error = parse(source).unwrap_err();
        assert!(
            error.message.contains("unknown escape"),
            "{source}: {error}"
        );
    }
}

#[test]
fn literal_errors_cover_the_literal_at_its_unicode_source_position() {
    let source = "value() -> (\"é\", '\\q')";
    let error = parse(source).unwrap_err();
    let start = source.find("'\\q'").unwrap();
    assert_eq!((error.offset, error.end), (start, start + 4));
    assert_eq!((error.line, error.column), (1, 18));
}

#[test]
fn a_discarded_value_must_be_an_effect_in_every_kind_of_body() {
    for source in [
        "value(x) ->\n  x\n  x",
        "value(x) ->\n  f(x)\n  x",
        "value(x) ->\n  x.f()\n  x",
        "T : Nat.(\n  value(x) ->\n    x\n    x\n)",
        "expect\n  True\n  True",
    ] {
        let error = parse(source).unwrap_err();
        assert!(
            error.message.contains("then thrown away"),
            "{source}: {error}"
        );
    }
    for source in [
        "value(x) ->\n  f!(x)\n  x",
        "value(x) ->\n  x.f!()\n  x",
        "value(x) ->\n  _ = f(x)\n  x",
        "value(x) -> x",
        "T : Nat.(\n  value(x) ->\n    f!(x)\n    x\n)",
        "expect\n  f!()\n  True",
    ] {
        parse(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}
