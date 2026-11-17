# Naming

This note owns how Faun names what a type or a library offers: the
standard library's conventions for conversions, questions, fallbacks and
errors, and where a library's names live, so a library reads like the
standard one. Rust's [API guidelines](https://rust-lang.github.io/api-guidelines/naming.html)
are the nearest counterpart; where Faun differs, it says why.

## Conversions

A conversion is named by the type it comes from or goes to:

- `T.of_x(x) -> T` makes a `T` from an `x`, always: `Int.of_nat`,
  `Set.of_list`, `F64.of_int`.
- `T.from_x(x) -> Result(T, …)` makes a `T` from an `x` where one fits,
  checked: `U8.from_nat`, `Nat.from_str`, `F64.from_nat`.
- `t.to_x() -> X` is an `X` from a `t`: `to_str`, `to_nat`, `to_list`,
  `to_bits`.

```ruby
expect U8.of_nat(300) == 44
expect U8.from_nat(300) == Err(TooBig)
expect Nat.from_str("42") == Ok(42)
expect U8.of_nat(300).to_nat() == 44
```

- `of_` never fails, and may lose what does not fit: `U8.of_nat` wraps and
  `F64.of_nat` rounds. Where nothing is lost, as in `Int.of_nat`, the name
  is the same.
- `from_` is the checked twin: it answers `Err` with why, rather than
  wrapping or rounding, and is what a value worked out at run time wants.
- `to_str` is also how a value prints itself: `"${value}"` calls it, and
  `Printable(a)` asks for it.

There is no `as_` and no `into_`. Rust tells a borrowed view, `as_`, from
a copy, `to_`, and from a conversion that takes ownership, `into_`; Faun's
types hold no borrows and its memory reuses what nothing else holds, so
the three are one, `to_`.

## Questions, fallbacks and failures

- `is_x` asks a yes-or-no question: `is_empty`, `is_ok`, `is_digit`,
  `is_nan`.
- A lookup that may find nothing answers a `Result`, `list.get(i)` and
  `map.get(key)`, and has no twin that takes a fallback: the fallback is
  `Result`'s, `list.get(i).ok_or(0)`, so every lookup gets it, and
  `?`, `|` and `map_ok` too, without each collection repeating them.
- `x_or(fallback)` answers the value, or the fallback where there is none:
  `ok_or`, `err_or`.
- `try_x` is the version of `x` that stops at the first `Err`: `try_map`,
  `try_fold`.
- A failure is a tag named by its cause, never text: `TooBig`,
  `Malformed`, `OutOfBounds`, `Missing`, `NotAscii`. Callers match on it,
  and two libraries refusing for one reason may share a word.
- A constant is a value on its type: `Nat.zero`, `Str.empty`.
- A verb names a function that does something, `encode`, `split`, `sort`;
  a noun names what it answers, `len`, `keys`, `first`. Neither takes a
  `get_` prefix.

## Operators

An operator is a method, `a | b` calling `a.or(b)`, so naming a method
`add`, `mul`, `or` and the rest gives a type the symbol too. Give one only
where it has one obvious meaning: closed, two of a type answering that
type, or else with the one partner the type is plainly used with, as a
price is scaled by a number. Where several meanings are natural, name them
instead. [Operators](operators.md) owns the conventions and their laws.

```ruby
expect (Nat.from_str("x") | Nat.from_str("7")) == Ok(7)
expect Nat.from_str("x").ok_or(0) == 0
```

`Result`'s `or` is the first `Ok`, closed as `|` is everywhere else; the
fallback to a plain value, which answers another type, is `ok_or`.

## Where names live

A type's block is its namespace: what concerns a type is a method of it,
called `value.method()` or `Type.method(…)`. A capitalised word before a
dot is a type and a lowercase one a value, so the case alone says which.

A library's other functions are exported plainly, `export {encode,
decode}`, and imported by name. Where two libraries export one name, the
importer renames one, `import base64 {encode: base64_encode}`; a library
does not prefix its names for it, nor declare a type only to hold them.

## Open questions

- **Whether `of_` should be lossless only.** `Int.of_nat` and `U8.of_nat`
  share a prefix, but only one can lose information, and the name does
  not say which. Rust keeps them apart, `From` for lossless conversions
  and `as` for lossy ones. Faun could keep `of_` for lossless conversions
  and name the lossy ones for what they do, `U8.wrapping(n)` and
  `F64.rounding(n)`.
