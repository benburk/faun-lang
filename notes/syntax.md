# Syntax

## Goals

- No symbol table required to parse it
- Fast to parse
- "layout"/indentation agnostic. indentation

## FAQ

> Why no commas?

- whitespace already separates lexical forms. A comma would repeat a boundary the parser has enough information to recognize
- One separator rule applies uniformly to values, types, patterns, fields, imports, exports, and dependencies. There is no second punctuation convention or trailing-comma policy to learn
- pro: narrower lines
- con: harder to read handwritten code
