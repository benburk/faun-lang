/**
 * @file Faun's grammar for tree-sitter, ported from
 * `crates/faun/src/grammar.ebnf`.
 *
 * The compiler's lexer decides what a line break and adjacency mean; here
 * `src/scanner.c` says where a line ends and whether a name's `!` is its
 * own, and `token.immediate` says what must stand against what it joins. A
 * line is one item whole, as in the EBNF: a body of several lines is a
 * block, `( )`, and a `where` list's constraints are parted by commas.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// Infix operators, loosest first, each level left-associative.
const INFIX = [
  ['|'],
  ['^'],
  ['&'],
  ['==', '!=', '<', '<=', '>', '>='],
  ['+', '-'],
  ['/', '%', '*'],
];

/**
 * One or more of `rule`, commas between, and perhaps one after.
 *
 * @param {RuleOrLiteral} rule
 */
function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)), optional(','));
}

/** @param {RuleOrLiteral} rule */
function commaSep(rule) {
  return optional(commaSep1(rule));
}

/**
 * Elements parted by commas, a rest only last: `{a, b, *rest}`.
 *
 * @param {RuleOrLiteral} element
 * @param {RuleOrLiteral} rest
 */
function elements(element, rest) {
  return seq(
    repeat(seq(element, ',')),
    optional(choice(element, seq(rest, optional(',')))),
  );
}

/**
 * A list's elements, its rest perhaps with more after it: `[a, *rest, b]`.
 *
 * @param {RuleOrLiteral} element
 * @param {RuleOrLiteral} rest
 */
function listElements(element, rest) {
  return seq(
    repeat(seq(element, ',')),
    optional(choice(element, seq(rest, optional(seq(',', commaSep(element)))))),
  );
}

/**
 * Lines parted by line ends, any of them empty.
 *
 * @param {GrammarSymbols<string>} $
 */
function lines($) {
  return seq(optional($._line), repeat(seq($._newline, optional($._line))));
}

module.exports = grammar({
  name: 'faun',

  // Where a line ends, and a name's `!`: see `src/scanner.c`. A block's
  // lines end apart from items', since a line beginning `if` goes on with
  // a clause above it and begins a block's next line.
  externals: $ => [$._newline, $.effect_identifier, $._block_newline],

  extras: $ => [/\s/, $.comment],

  word: $ => $.identifier,

  supertypes: $ => [$._expression, $._type],

  // `Name(a)` begins an alias or a declaration, and which only the `=` or
  // `:` after it says.
  conflicts: $ => [[$.type_alias, $._primary]],

  rules: {
    source_file: $ => lines($),

    _line: $ => choice(
      $.package,
      $.import,
      $.export,
      $.expect,
      $.type_alias,
      $.signature,
      $.clause,
      $.value,
    ),

    // Directives.

    package: $ => seq('package', '{', commaSep($.dependency), '}'),

    dependency: $ => seq(
      field('name', $.identifier),
      ':',
      field('path', $.string),
    ),

    import: $ => seq(
      'import',
      field('module', $.module_path),
      '{',
      commaSep($.exposure),
      '}',
    ),

    module_path: $ => seq($.identifier, repeat(seq('.', $.identifier))),

    export: $ => seq('export', '{', commaSep($.exposure), '}'),

    exposure: $ => seq(
      field('name', $._any_name),
      optional('.*'),
      optional(seq(':', field('alias', $._any_name))),
    ),

    _any_name: $ => choice($.identifier, $.effect_identifier, $.type_identifier),

    // Lines headed by an expression, told apart by what follows it. A
    // pattern is written as the expression that builds what it matches.

    expect: $ => seq('expect', $._expression),

    // After a type's name, and its parameters, `=` names a type.
    type_alias: $ => seq(
      field('name', $.type_identifier),
      optional(field('parameters', $.type_parameters)),
      '=',
      field('type', choice($._type, $.constraints)),
    ),

    type_parameters: $ => seq(
      $._call_paren,
      commaSep1(alias($.identifier, $.type_variable)),
      ')',
    ),

    signature: $ => seq(
      field('name', $._expression),
      ':',
      field('type', $._type),
      optional($.constraints),
      optional($.methods),
    ),

    binding: $ => seq(
      field('pattern', $._expression),
      '=',
      field('value', choice($._expression, $.constraints)),
    ),

    clause: $ => seq(
      field('head', $._expression),
      optional($.guard),
      '->',
      field('body', $._expression),
    ),

    guard: $ => seq('if', $._expression),

    // After a value's name, `=` gives the value: a definition of no
    // parameters.
    value: $ => seq(
      field('name', $.identifier),
      '=',
      field('value', $._expression),
    ),

    // A type's methods: lines in `.( )`.
    methods: $ => seq('.(', lines($), ')'),

    // Constraints: `where Show(a), a.show : a -> Str`.

    constraints: $ => seq(
      'where',
      $._constraint,
      repeat(seq(',', $._constraint)),
    ),

    _constraint: $ => choice($.class_constraint, $.member_constraint),

    class_constraint: $ => seq(
      field('class', $.type_identifier),
      field('arguments', $.type_arguments),
    ),

    member_constraint: $ => seq(
      field('type', alias($.identifier, $.type_variable)),
      '.',
      field('member', choice($.identifier, $.effect_identifier)),
      ':',
      field('signature', $._type),
    ),

    // Types. A function type's parameters are the parenthesized types before
    // its arrow, or the one type there.

    _type: $ => choice($.function_type, $._type_operand),

    function_type: $ => seq(
      field('parameters', $._type_operand),
      '->',
      field('result', $._type_operand),
    ),

    _type_operand: $ => choice(
      $.generic_type,
      $.type_identifier,
      alias($.identifier, $.type_variable),
      $.wildcard,
      $.tuple_type,
      $.variant_type,
      $.record_type,
    ),

    generic_type: $ => seq(
      field('name', $.type_identifier),
      field('arguments', $.type_arguments),
    ),

    type_arguments: $ => seq($._call_paren, commaSep1($._type), ')'),

    tuple_type: $ => seq('(', commaSep1($._type), ')'),

    variant_type: $ => seq('[', commaSep($.variant), ']'),

    variant: $ => seq(
      field('name', $.type_identifier),
      optional(field('arguments', $.type_arguments)),
    ),

    record_type: $ => seq('{', elements($.field_type, $.rest), '}'),

    field_type: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._type),
    ),

    // Expressions.

    // An `if` takes everything after its `else`, so nothing follows it.
    _expression: $ => choice(
      $.binary_expression,
      $.is_expression,
      $._operand,
      $.if_expression,
      $.return_expression,
    ),

    // A block's line: go on where the condition holds, else leave.
    expect_line: $ => seq(
      'expect',
      field('condition', $._expression),
      'else',
      field('otherwise', $._expression),
    ),

    return_expression: $ => prec.right(seq('return', field('value', $._expression))),

    binary_expression: $ => choice(...INFIX.map((operators, level) =>
      prec.left(level + 1 + (level >= 3 ? 1 : 0), seq(
        field('left', $._expression),
        field('operator', operators.length === 1 ? operators[0] : choice(...operators)),
        field('right', $._expression),
      )),
    )),

    // `value is pattern`, between `&` and the comparisons; its pattern is
    // one operand.
    is_expression: $ => prec.left(4, seq(
      field('value', $._expression),
      'is',
      field('pattern', $._operand),
    )),

    _operand: $ => choice($.unary_expression, $.equal_pattern, $._postfix),

    // A pattern's: a value equal to the name.
    equal_pattern: $ => seq('==', field('name', $.identifier)),

    unary_expression: $ => seq(
      field('operator', choice('-', '!')),
      field('operand', $._operand),
    ),

    _postfix: $ => choice(
      $.call_expression,
      $.field_expression,
      $.try_expression,
      $._primary,
    ),

    call_expression: $ => seq(
      field('function', $._postfix),
      field('arguments', $.arguments),
    ),

    arguments: $ => seq(
      $._call_paren,
      commaSep(choice($.lambda, $._expression)),
      ')',
    ),

    lambda: $ => seq(
      field('parameters', $.lambda_parameters),
      field('body', $._expression),
    ),

    lambda_parameters: $ => seq('|', commaSep1($._operand), '|'),

    field_expression: $ => seq(
      field('value', $._postfix),
      '.',
      field('field', choice($.identifier, $.effect_identifier, $.type_identifier)),
    ),

    try_expression: $ => seq($._postfix, token.immediate('?')),

    _primary: $ => choice(
      $.identifier,
      $.effect_identifier,
      $.type_identifier,
      $.number,
      $.decimal,
      $.char,
      $.wildcard,
      $.range,
      $.string,
      $.tuple,
      $.block,
      $.list,
      $.record,
    ),

    // Its `else` as far as an expression goes.
    if_expression: $ => prec.right(seq(
      'if',
      field('condition', $._expression),
      'then',
      field('consequence', $._expression),
      'else',
      field('alternative', $._expression),
    )),

    // A range's end may be negated, or `_` to leave that side open.
    range: $ => seq(
      field('start', choice($.number, $.char, $.wildcard)),
      '..',
      field('end', choice(
        $.number,
        $.char,
        $.wildcard,
        alias($._negative_bound, $.unary_expression),
      )),
    ),

    _negative_bound: $ => seq(
      field('operator', '-'),
      field('operand', choice($.number, $.char)),
    ),

    tuple: $ => seq('(', commaSep1($._expression), ')'),

    // Bindings, then the answer, a line apiece; a line before the last that
    // binds nothing is an effect asked for what it does.
    block: $ => seq(
      '(',
      repeat1(seq(choice($.binding, $.expect_line, $._expression), $._block_newline)),
      field('answer', $._expression),
      ')',
    ),

    list: $ => seq('[', listElements($._expression, $.rest), ']'),

    record: $ => seq('{', elements($.field, $.rest), '}'),

    field: $ => seq(
      field('name', $.identifier),
      optional(seq(':', field('value', $._expression))),
    ),

    rest: $ => seq('*', optional($._expression)),

    // Strings: text, escapes, and `${…}` splices of ordinary expressions.

    string: $ => seq(
      '"',
      repeat(choice(
        $.string_content,
        alias(token.immediate('$'), $.string_content),
        $.escape_sequence,
        $.interpolation,
      )),
      token.immediate('"'),
    ),

    string_content: _ => token.immediate(prec(1, /[^"\\$]+/)),

    escape_sequence: _ => token.immediate(prec(1, /\\(u\{[0-9a-fA-F]+\}|.)/)),

    interpolation: $ => seq(
      token.immediate(prec(1, '${')),
      $._expression,
      optional($.width),
      '}',
    ),

    // A splice's width: `<` keeps its text left, `>` right.
    width: $ => seq(':', choice('<', '>'), $.number),

    // Tokens.

    // `(` straight after an operand: a call's, or a type's.
    _call_paren: _ => token.immediate('('),

    identifier: _ => /[a-z_][a-zA-Z0-9_]*/,

    type_identifier: _ => /[A-Z][a-zA-Z0-9_]*/,

    wildcard: _ => '_',

    number: _ => /0x[0-9a-fA-F]+|0b[01]+|[0-9]+/,

    decimal: _ => /[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/,

    char: _ => /'([^'\\\r\n]|\\(u\{[0-9a-fA-F]+\}|.))'/,

    comment: _ => token(seq('#', /.*/)),
  },
});
