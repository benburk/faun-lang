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
        "expected one of `(`, `[`, `_`, `{`, a name, a type name before the end of the file"
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
}

#[test]
fn a_body_of_several_lines_is_a_block() {
    for (source, said) in [
        ("f(x) ->\n  y = x\n  y\n", "a binding belongs to a block"),
        (
            "expect\n  y = 1\n  y == 1\n",
            "a binding belongs to a block",
        ),
        ("f(x) -> x\n  x\n", "belongs to no definition"),
        (
            "f(x) -> (\n  y = x\n  y\ng(x) -> x\n",
            "this `(` is not closed: its block runs on into the next item",
        ),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
}

#[test]
fn a_definition_of_no_parameters_is_a_value() {
    let read = clauses("origin = (0, 0)\n");
    assert!(read[0].patterns.is_empty());
    for (source, said) in [
        (
            "origin() -> (0, 0)\n",
            "a definition of no parameters is a value: `origin = ...`",
        ),
        ("(x, y) = (0, 0)\n", "begins with the name it defines"),
        ("(origin) = (0, 0)\n", "begins with the name it defines"),
        ("f(x).y -> 1\n", "expected one of"),
        ("Origin = (0, 0)\n", "expected"),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
}

#[test]
fn a_block_stands_wherever_an_expression_does() {
    let lines = body("f(x) -> [1].map(|y| (\n  z = y\n  z + x\n))\n");
    let ExprKind::Method(_, _, arguments) = &lines.result.kind else {
        panic!("a method call, found {:?}", lines.result.kind);
    };
    assert!(matches!(
        &arguments[0].kind,
        ExprKind::Lambda(_, body) if matches!(&body.kind, ExprKind::Block(block) if block.bindings.len() == 1)
    ));
    let read = clauses("f(x) if (\n  y = x\n  y > 1\n) -> x\n");
    assert!(matches!(
        read[0].guard.as_ref().map(|guard| &guard.kind),
        Some(ExprKind::Block(_))
    ));
    let lines = body("f(x) -> (\n  y = (\n    z = x\n    z\n  )\n  (y, (y))\n)\n");
    assert!(matches!(lines.bindings[0].value.kind, ExprKind::Block(_)));
    assert!(matches!(lines.result.kind, ExprKind::Tuple(ref members) if members.len() == 2));
}

#[test]
fn a_body_is_its_lines_and_its_last_line_is_its_answer() {
    let lines = body("f(x) -> (\n  log!(x)\n  y = x\n  -y\n)\n");
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
        "sum : List(a) -> a where\n  a.zero : a,\n  a.add : (a, a) -> a\nsum(values) -> values\n",
    )
    .unwrap();
    assert!(matches!(
        &module.items[0],
        Item::Signature(signature) if signature.constraints.len() == 2
    ));
}

#[test]
fn a_where_list_s_constraints_are_parted_by_commas() {
    let module = parse("f : a -> a where a.zero : a, Show(a), a.add : (a, a) -> a\n").unwrap();
    assert!(matches!(
        &module.items[0],
        Item::Signature(signature) if signature.constraints.len() == 3
    ));
    for (source, said) in [
        (
            "f : a -> a where\n  a.zero : a\n  a.add : (a, a) -> a\n",
            "parted by commas",
        ),
        (
            "f : a -> a where\n  a.zero : a,\nf(x) -> x\n",
            "last constraint takes no comma",
        ),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
}

#[test]
fn elements_are_parted_by_commas_however_they_are_spaced() {
    let lines = body("f(a, b) ->\n  [a - b, a- b, a-b,]\n");
    assert!(matches!(
        lines.result.kind,
        ExprKind::List(ref elements, None) if elements.len() == 3
            && elements.iter().all(|element| matches!(element.kind, ExprKind::Binary(..)))
    ));
    // A prefix touches what it takes, so `a -b` would be two values.
    for (source, said) in [
        ("f(a, b) -> [a -b]\n", "touches what it negates"),
        ("f(a) -> - a\n", "touches what it negates"),
        ("f(a) -> ! a\n", "touches what it negates"),
        ("f(a, b) -> [a *b]\n", "touches the rest it takes"),
        ("f([a, * rest]) -> a\n", "touches the rest it takes"),
        (
            "f(a, b) -> a ==b\n",
            "touches the name a pattern compares with",
        ),
        (
            "f(xs, b) -> xs is [== b]\n",
            "touches the name a pattern compares with",
        ),
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.message.contains(said), "{source}: {}", error.message);
    }
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
    let lines = body("f(xs) -> (\n  Some(y) = xs.first()\n  xs.map(|Some(z), _| z)\n)\n");
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

/// A file that is not Faun is read for its first twenty errors and no
/// further, each of which would otherwise cost as much as the text before it.
#[test]
fn a_file_is_read_no_further_than_its_first_twenty_errors() {
    let error = parse(&"x = )\n".repeat(25)).unwrap_err();
    assert_eq!(error.also.len() + 1, 20);
    assert_eq!(error.also.last().map(|last| last.line), Some(20));
    assert!(
        error
            .advice
            .notes
            .iter()
            .any(|note| note.contains("first 20 errors")),
        "{:?}",
        error.advice.notes
    );
}

/// An error inside a block passes over the rest of the line holding it,
/// so the block's later lines are not read as lines of the file.
#[test]
fn an_error_inside_a_block_passes_over_its_line_whole() {
    let error = parse(
        "f(x) -> (\n  y = x is (\n    0 then (\n      z = 1 1\n    )\n    _ then 2\n  )\n  y\n)\ng(y) -> y +\n",
    )
    .unwrap_err();
    let told: Vec<_> = std::iter::once(&error)
        .chain(&error.also)
        .map(|error| (error.line, error.message.as_str()))
        .collect();
    assert_eq!(told.len(), 2, "{told:?}");
    assert_eq!(told[0].0, 4, "{told:?}");
    assert_eq!(told[1].0, 11);
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
        "f(Some(x), y) if x > 1 & y.ok() | !x -> (\n  z = x\n  z\n)\nf(_, _) -> 0\ng(x) if\n  x -> x\n",
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
    for suffix in ["", "\ntext = \"text\"", "\ncharacter = 'x'"] {
        for exponent in ["10001", "-10001", "4294967296"] {
            let source = format!("number = 1.0e{exponent}{suffix}");
            let error = parse(&source).unwrap_err();
            assert!(error.message.contains("reaches past 10000"), "{error}");
            assert_eq!((error.line, error.column), (1, 10));
        }
    }
    for exponent in ["10000", "-10000"] {
        parse(&format!("number = 1.0e{exponent}")).unwrap();
    }
}

#[test]
fn literal_validation_reaches_every_syntactic_position() {
    for source in [
        r#"value = "\q""#,
        r#"match("\q") -> 0"#,
        r"match('\q'..'z') -> 0",
        r"match(x) if x == '\q' -> 0",
        "value = (\n  x = '\\q'\n  x\n)",
        r"value = map(|'\q'| 0)",
        r#"value = "${'\q'}""#,
        r#"value = "${"\q"}""#,
        "T : Nat.(\n  value = \"\\q\"\n)",
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
    let source = "value = (\"é\", '\\q')";
    let error = parse(source).unwrap_err();
    let start = source.find("'\\q'").unwrap();
    assert_eq!((error.offset, error.end), (start, start + 4));
    assert_eq!((error.line, error.column), (1, 15));
}

#[test]
fn a_discarded_value_must_be_an_effect_in_every_kind_of_body() {
    for source in [
        "value(x) -> (\n  x\n  x\n)",
        "value(x) -> (\n  f(x)\n  x\n)",
        "value(x) -> (\n  x.f()\n  x\n)",
        "T : Nat.(\n  value(x) -> (\n    x\n    x\n  )\n)",
        "expect (\n  True\n  True\n)",
        "value(x) -> [(\n  x\n  x\n)]",
        "value(x) -> (\n  f(x)?\n  x\n)",
    ] {
        let error = parse(source).unwrap_err();
        assert!(
            error.message.contains("then thrown away"),
            "{source}: {error}"
        );
    }
    for source in [
        "value(x) -> (\n  f!(x)\n  x\n)",
        "value(x) -> (\n  x.f!()\n  x\n)",
        "value(x) -> (\n  f!(x)?\n  x\n)",
        "value(x) -> (\n  x.f!()?\n  x\n)",
        "value(x) -> (\n  _ = f(x)\n  x\n)",
        "value(x) -> x",
        "T : Nat.(\n  value(x) -> (\n    f!(x)\n    x\n  )\n)",
        "expect (\n  f!()\n  True\n)",
    ] {
        parse(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

/// An `if` takes everything after its `else`, so as an operand it is
/// refused, saying to put it in parentheses, and in parentheses it is read.
#[test]
fn an_if_as_an_operand_is_written_in_parentheses() {
    let error = parse("offset(late) -> 1 + if late then 10 else 0").unwrap_err();
    assert!(error.message.contains("written in parentheses"), "{error}");
    assert!(parse("offset(late) -> 1 + (if late then 10 else 0)").is_ok());
}

/// A test answers a `Bool`, so testing it again or comparing it is refused,
/// each saying what to write instead.
#[test]
fn a_test_is_not_tested_again_or_compared() {
    let error = parse("f(x) -> x is A is B").unwrap_err();
    assert!(error.message.contains("join tests with `&`"), "{error}");
    let error = parse("f(x) -> x is 3 == y").unwrap_err();
    assert!(error.message.contains("put it in parentheses"), "{error}");
    assert!(parse("f(x) -> (x is 3) == y").is_ok());
}

/// A block answers its last line where that is a value, and `{}` where it
/// is a binding, a leaving line or a loop; a round goes on to the next.
#[test]
fn a_block_ending_in_no_value_answers_nothing() {
    for source in [
        "f(x) -> (\n  y = x\n)",
        "f(x) -> (y = x)",
        "f(x) -> (\n  y = x\n  y > 0 else return 0\n)",
        "f(x) -> (\n  y = x\n  if y return 0\n)",
        "f(x) -> (\n  for y in x do (\n    if y break\n  )\n)",
    ] {
        let clause = clauses(source).remove(0);
        let mut answer = &clause.body.result;
        loop {
            answer = match &answer.kind {
                ExprKind::Block(body)
                | ExprKind::Else { rest: body, .. }
                | ExprKind::Leave { rest: body, .. }
                | ExprKind::Loop { rest: body, .. } => &body.result,
                _ => break,
            };
        }
        assert!(
            matches!(&answer.kind, ExprKind::Record(fields) if fields.is_empty()),
            "{source}: {answer:?}"
        );
    }
    assert!(parse("f(x) -> (\n  for y in x do (\n    y = 1\n  )\n  0\n)").is_ok());
}

/// A parenthesis holds lines; a tuple's member and an arm's pattern are
/// values, so a binding, a leaving line or a loop before a `,` or `->` is
/// refused, saying where it stands.
#[test]
fn a_tuple_s_member_and_an_arm_s_pattern_are_values() {
    for source in [
        "f(x) -> (y = x, 2)",
        "f(x) -> (x > 0 else return 0, 2)",
        "f(x) -> (if x return 0, 2)",
    ] {
        let error = parse(source).unwrap_err();
        assert!(
            error.message.contains("a tuple's member is a value"),
            "{error}"
        );
    }
    let error = parse("f(x) -> x is (\n  y = 1 then y\n)").unwrap_err();
    assert!(
        error.message.contains("an arm's pattern is a value"),
        "{error}"
    );
    assert!(parse("f(x) -> (if x then 1 else 2, 3)").is_ok());
}

/// A lambda stands only as an argument, with a parameter or more, and a
/// list holds one rest; each refusal says what to write instead.
#[test]
fn a_lambda_is_an_argument_and_a_list_holds_one_rest() {
    let error = parse("f(n) -> (|x| x + 1)(n)\n").unwrap_err();
    assert!(
        error.message.contains("only as a call's argument"),
        "{error}"
    );
    let error = parse("f(n) -> [n].map(|| 3)\n").unwrap_err();
    assert!(error.message.contains("one parameter or more"), "{error}");
    let error = parse("f(a, b) -> a | | b\n").unwrap_err();
    assert!(error.message.contains("expected"), "{error}");
    let error = parse("f(xs) -> [*xs, *xs]\n").unwrap_err();
    assert!(error.message.contains("one rest"), "{error}");
    assert!(parse("f(xs) -> [[*xs], *xs]\n").is_ok());
}

/// `==name` compares a part, so an arm cannot begin with one, and the
/// message says how to compare the whole value.
#[test]
fn an_arm_does_not_begin_with_equals() {
    let error = parse("f(n) -> n is (\n  0 then 1\n  ==limit then 2\n  _ then 3\n)").unwrap_err();
    assert!(error.message.contains("no line begins"), "{error}");
    assert!(parse("f(n) -> n is (\n  0 then 1\n    == 2\n  _ then 3\n)").is_ok());
}

/// A body leaves only by a leaving line, whose `else` is followed by a
/// leave: `return` stands nowhere else, and an `else` going on is refused.
#[test]
fn a_body_leaves_only_by_a_leaving_line() {
    let error = parse("f(n) -> return n").unwrap_err();
    assert!(error.message.contains("only by a leaving line"), "{error}");
    let error = parse("f(xs) -> (\n  for x in xs do (\n    break\n  )\n  0\n)").unwrap_err();
    assert!(error.message.contains("`if c break`"), "{error}");
    let error = parse("f(n) -> (\n  n > 0 else 0\n  n\n)").unwrap_err();
    assert!(error.message.contains("`return`"), "{error}");
    let error = parse("f(xs) -> (\n  for x in xs (\n    if x break\n  )\n  0\n)").unwrap_err();
    assert!(error.message.contains("touches what it calls"), "{error}");
    let error = parse("f(xs) -> (\n  for x in xs do log!(x)\n  0\n)").unwrap_err();
    assert!(
        format!("{error:?}").contains("lines in parentheses"),
        "{error:?}"
    );
    let error = parse("f(x) -> g (x)").unwrap_err();
    assert!(error.message.contains("touches what it calls"), "{error}");
}

/// An arm's value follows `then`, or the arm leaves, where the `is` is a
/// line's value or a body's answer; on a line of its own, arms go on with
/// `{}`.
#[test]
fn an_arm_answers_after_then_or_leaves() {
    let bound = "f(r) -> (\n  y = r is (\n    Ok(v) then v\n    Err(e) return 0\n  )\n  y\n)\n";
    assert!(parse(bound).is_ok());
    let alone = "f(xs) -> (\n  for x in xs do (\n    x is (\n      0 break\n      _ then {}\n    )\n  )\n  0\n)\n";
    let module = parse(alone).unwrap();
    assert!(format!("{module:?}").contains("open: false"), "{module:?}");
    let error = parse("f(r) -> g(r is (\n  Ok(v) then v\n  Err(_) return 0\n))\n").unwrap_err();
    assert!(
        error.message.contains("an arm leaves only where"),
        "{error}"
    );
    let error = parse("f(r) -> r is (\n  Ok(v) -> v\n)\n").unwrap_err();
    assert!(error.message.contains("follows `then`"), "{error}");
}
