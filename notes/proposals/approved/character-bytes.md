# Proposal: A character at a byte is ASCII

- **Status:** Approved
- **Created:** 2026-11-04
- **Approved:** 2026-11-04
- **Affects:** the checker's numerals, the lexer's character literals, the
  refused programs, `notes/values/strings.md`

---

## Summary

A character literal whose position makes it a `U8` must be ASCII, a scalar
below 128. Anything else is refused, with its UTF-8 bytes shown.

| Written            | Before        | After             |
| ------------------ | ------------- | ----------------- |
| `'a'` at a `U8`    | 97            | 97                |
| `'é'` at a `U8`    | 233           | refused           |
| `'€'` at a `U8`    | out of range  | refused, as `'é'` |
| `'é'` at a `U32`   | 233           | 233               |
| `'\u{e9}'` written | invalid token | the scalar 233    |

## Motivation

`Str` is UTF-8 bytes, so a `U8` compared with a character is a byte of
UTF-8 text. A byte from 128 to 255 is never a whole character in UTF-8, so
a character literal there could only be a mistake: `'é'` was accepted as
233, `é` only in Latin-1, and `byte == 'é'` compiled and could never match
a byte of a Faun string, which holds `é` as `0xc3` then `0xa9`. No program
in the corpus wrote a non-ASCII character literal at any type.

## Design

- **The rule.** At a `U8`, a character literal is checked before its range:
  a scalar of 128 or more is refused, whatever its size.
- **The message.** It says the character is not one byte in UTF-8, gives
  its bytes, and offers the byte by number where one is below 256, and the
  encoding by `to_utf8` always:

  ```
  error: `'é'` is not one byte in UTF-8, so it cannot be a `U8`
    = note: `'é'` is 2 bytes in UTF-8: `[0xc3, 0xa9]`
    = help: write `0xe9` for the byte 233, or `"é".to_utf8()` for its encoding
  ```

- **Where it applies.** Expressions, patterns, range ends, and a generic
  definition's character specialized at a `U8`. At `Nat`, `Int`, `U16`,
  `U32` and `U64` a character is its scalar value, as before.
- **Characters by number.** The lexer reads `'\u{…}'`, as the standard
  README and the tree-sitter grammar already said it did, so a character
  that does not print can be written and refused alike.

## Costs

A program that means the Latin-1 byte writes it by number, `0xe9`. Nothing
in the corpus changed.

## Alternatives considered

- **Keep it.** The mismatch stays silent, in exactly the code that compares
  bytes with characters.
- **Make `'é'` at a `U8` its UTF-8 bytes.** A character would then be a
  list where a byte is wanted, which no position can hold.

## Origin

Found while writing the strings note, which had to describe `'é'` at a
`U8` as 233 beside `"é".to_utf8()` as `[0xc3, 0xa9]`.
