; Most general first: where two patterns capture one node, Helix takes the
; later.

; Names

(identifier) @variable

; An effect is marked as a Rust macro is: `print!`.
(effect_identifier) @function.macro

(type_identifier) @constructor

(type_variable) @type.parameter

; `_` reads as the names a pattern binds do.
(wildcard) @variable

((type_identifier) @constant.builtin.boolean
  (#any-of? @constant.builtin.boolean "True" "False"))

(module_path
  (identifier) @namespace)

(dependency
  name: (identifier) @namespace)

; Fields

(field_expression
  field: (identifier) @variable.other.member)

(field
  name: (identifier) @variable.other.member)

(field_type
  name: (identifier) @variable.other.member)

; Types

(signature
  type: (type_identifier) @type)

(function_type
  (type_identifier) @type)

(type_arguments
  (type_identifier) @type)

(tuple_type
  (type_identifier) @type)

(field_type
  type: (type_identifier) @type)

(member_constraint
  signature: (type_identifier) @type)

(generic_type
  name: (type_identifier) @type)

(class_constraint
  class: (type_identifier) @type)

(type_alias
  name: (type_identifier) @type)

(type_alias
  type: (type_identifier) @type)

(variant
  name: (type_identifier) @type.enum.variant)

; A declaration's name, and its parameters: `Stack(a) : [...]`.
(signature
  name: (type_identifier) @type)

(signature
  name: (call_expression
    function: (type_identifier) @type
    arguments: (arguments
      (identifier) @type.parameter)))

; Functions

(call_expression
  function: (identifier) @function)

(call_expression
  function: (field_expression
    field: (identifier) @function.method))

(signature
  name: (identifier) @function)

(clause
  head: (call_expression
    function: (identifier) @function))

(value
  name: (identifier) @constant)

(member_constraint
  member: (identifier) @function.method)

; A pattern's names stay variables: a query reaches only a fixed depth, so
; marking parameters would mark `y` in `add(Succ(n), y)` but not `n`.

; Literals

(number) @constant.numeric.integer

(decimal) @constant.numeric.float

(char) @constant.character

(string) @string

(escape_sequence) @constant.character.escape

(comment) @comment.line

; Keywords

[
  "package"
  "import"
  "export"
] @keyword.control.import

"if" @keyword.control.conditional

[
  "where"
  "expect"
] @keyword

; Operators and punctuation

[
  "|"
  "^"
  "&"
  "=="
  "!="
  "<"
  "<="
  ">"
  ">="
  "+"
  "-"
  "/"
  "%"
  "*"
  "!"
  "?"
  ".."
  "->"
  "="
] @operator

[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
  ".("
] @punctuation.bracket

[
  ","
  "."
  ":"
  ".*"
] @punctuation.delimiter

(lambda_parameters
  "|" @punctuation.bracket)

(interpolation
  [
    "${"
    "}"
  ] @punctuation.special)

(width
  [
    ":"
    "<"
    ">"
  ] @punctuation.special)
