# faun

The Faun frontend: it reads a package, checks it, and lowers an
application to [Barb](../barb/README.md).

Every error a programmer can cause is found here. What comes out is plain
Barb: typed, monomorphized, first-order, with no syntax sugar left. Below
the frontend, a program is only refused for what its target cannot do.

## API

| Function              | Takes          | Answers                       |
| --------------------- | -------------- | ----------------------------- |
| `check_package`       | a package      | `Library`, or `Application`   |
| `lower_to_barb`       | an application | its Barb, before optimization |
| `lower_tests_to_barb` | a package      | Barb running its `expect`s    |
| `compile_to_image`    | an application | a target's image              |

Each also takes the target. `Library` and `Application` are the two cases
of `Package`; an application carries its Barb.

A package whose entry defines `main!` is an application. One that doesn't
is a library, and the frontend's checks are all a library has: it never
becomes Barb. The target matters to the frontend only through its host
module, which says what `Host` offers, and the routines it provides.

## What it checks

- **Names.** Every name is declared once and resolves.
- **Types.** Hindley–Milner inference, with rows, and methods resolved by
  their receiver.
- **Coverage.** Clauses and arms cover what they take apart.
- **Functions are second class.** A function is handed to a call, never
  held as a value.
- **Resources.** A resource is used up exactly once.
- **Effects.** An effect is a name ending in `!`, and effects stand one to a
  line.
- **The entry.** `main!` and the host meet the application's ABI.

## What it hands Barb

- Every definition at concrete types: monomorphized.
- No function values: each set of callbacks a function is handed gets a
  definition of its own.
- Every call and construction saturated, every match covering its type.
- Exactly one entry, `main!`'s.
- Nothing about what a function means. Barb recognizes that from the code.

## What's blessed

Some syntax has to turn into something, and the language says what. A
blessing chooses that target and nothing more: it never says what a
function means or makes one fast. All of them live in `blessed.rs`, and
the rest of the frontend uses the symbols it resolves, never a spelling.

### Literals to standard types

| Literal                    | May be                                  |
| -------------------------- | --------------------------------------- |
| `3`, `0xff`, `0b11`, `'a'` | `Nat`, `Int`, `U8`, `U16`, `U32`, `U64` |
| `-3`                       | one of those, through its `neg`         |
| `1.5`                      | `F64` or `F32`                          |
| `"text"`                   | `Str`                                   |
| `[a, b]`                   | `List`                                  |

A numeral's position decides its type. Where nothing does, it's a `Nat`, a
negated one an `Int`, and a decimal an `F64`.

### Sugar to standard calls

Sugar is desugared as soon as the frontend knows enough, which for most of
it means once types are known.

| Syntax                  | Becomes                                | Stage |
| ----------------------- | -------------------------------------- | ----- |
| a numeral at `T`        | `T.of_nat` or `of_decimal`, and `neg`  | 3     |
| `a + b`, `-`, `*`, …    | `a.add(b)`, `sub`, `mul`, `div`, `mod` | 3     |
| `a & b`, `\|`, `^`      | `a.and(b)`, `or`, `xor`, off `Bool`    | 3     |
| `a == b`, `a != b`      | `a.equals(b)`, then `Bool.not`         | 3     |
| `a < b`, `<=`, …        | `a.cmp(b)`, then `Order.lt`, `le`, …   | 3     |
| `-a`, `!a`              | `a.neg()`, `a.not()`                   | 3     |
| `"${x}"`                | `x.to_str()`, joined by `Str.concat`   | 2     |
| `a & b`, `\|` on `Bool` | a match on `a`, `b` only if needed     | 4     |
| `[*front, last]`        | `List.len`, `take` and `drop`          | 4     |
| `"text"` as a pattern   | `Str.equals`                           | 4     |
| `lo..hi` as a pattern   | the type's `cmp`, then `Order.le`      | 4     |
| `x?`                    | a match on `Result`'s `Ok` and `Err`   | 7     |

The stage that desugars each is numbered as under [Stages](#stages).

Records, tuples and tag rows get `equals`, `cmp`, `to_str` and
`hash_into` without declaring them, built from their parts. A type that
declares `cmp` gets an `equals` from it.

## Stages

Each stage takes the program as one tree.

1. **Loading** reads every module of the package and the packages it names.
2. **Resolution** names every global and local, and finds the blessed items.
3. **Checking** infers types, writes the members a type asks for, and checks
   coverage.
4. **Specialization** makes each definition concrete at every type it's
   used at.
5. **Callback lowering** gives each set of callbacks its own definition, so
   no value is a function. Resources are then checked.
6. **Pattern compilation** turns clauses into decisions. A library stops
   here.
7. **Barb lowering** writes an application as Barb and validates it.
