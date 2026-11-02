# Tags

A tag is a capitalised word naming one case of a value: `Ok`, `Empty`,
`NotFound`, `Circle(r)`. This note owns the two kinds of tag, structural and
nominal, the rows that structural tags form, how a word that could be either
is resolved, and how a module keeps its constructors to itself.

## Structural tags

A capitalised word that no visible declaration claims is a structural tag.
It exists by being written: it belongs to no module, needs no import, and is
identified by its spelling and its payload types. The standard list's
`first` is one:

```ruby
first : List(a) -> Result(a, [Empty])
first([]) -> Err(Empty)
first([head, *_]) -> Ok(head)
```

`[Empty]` is a variant row: a set of tags, each with its payload types. Rows
are row-polymorphic, which means a type may hold "these tags, and whatever
else is joined to them" while inference works it out. Where two rows meet,
unification joins them into one row holding the tags of both:

```ruby
MyError = [NotFound, SomethingElse]
AnotherError = [Blah, NotFound]

cat : Nat -> Result(Nat, MyError)
dog : Nat -> Result(Nat, AnotherError)

foo : Nat -> Result(Nat, [Blah, NotFound, SomethingElse])
foo(n) -> (
  x = cat(n)?
  y = dog(n)?
  Ok(x + y)
)
```

Each `?` adds its producer's failure tags to the answer's row, and the two
`NotFound`s are one tag. No umbrella type and no conversion take part. The
same word may carry different payloads in rows that never meet. Where they
do meet, the payloads must unify: joining `[Invalid(Nat), Missing]` with
`[Denied, Invalid(Str)]` is refused, since one row cannot hold two
`Invalid`s.

A caller that needs to know which producer failed wraps each at the join.
A tag may be passed as a callback for this:

```ruby
combined(n) -> (
  x = cat(n).map_err(CatFailure)?
  y = dog(n).map_err(DogFailure)?
  Ok(x + y)
)
```

The row now holds `CatFailure(...)` and `DogFailure(...)`, and the inner
`NotFound`s stay one tag.

### Closed and open

A row written in a signature is closed for the body and open to callers.
The body may answer only those tags: `first([]) -> Err(Nope)` under
`[Empty]` is refused with `` `Nope` is not among the tags of `[Empty]` ``.
A caller may still join `first`'s row with its own. A row in a parameter is
what the definition handles, and stays closed. Clauses that take a row apart
with no catch-all close it too, so after `f(A) -> 1` and `f(B) -> 2`, the
call `f(C)` is refused.

A signature may write `_` for a row it leaves to its `?`s:
`parse_pair : (Str, Str) -> Result((Nat, Nat), _)` answers whatever its
producers and its own `Err(Zero)` join.

A closed row has `equals` and `to_str` without declaring them. Two values
are equal where they are one tag with equal payloads, and a tag is written
as its name with its payloads after it: `Invalid(3)`.

## Nominal types

A capitalised `:` declaration mints a type and its constructors:

```ruby
Light : [Low, High]
Tree(a) : [Leaf, Node(Tree(a), a, Tree(a))]
Email : Str
```

`Email : Str` is short for a type with one constructor, `Email(Str)`. A
constructor belongs to its type, so `Match` and `Parse` may both declare
`Failed` and stay apart. A nominal type never unifies with a structural row
of the same shape. Methods, and the derived `equals`, `cmp`, `to_str` and
`hash_into`, live in the type's block ([methods](../forms/methods.md)). A
sum's own name may stand for all its constructors in a clause's parameters,
which is how a sum forwards a method to whichever value it holds; that is
the methods note's too.

## Resolution by position

A word that some visible declaration also claims is read as its position's
type decides. A position that wants a row takes the structural tag. A
position that wants a nominal type takes that type's constructor. Both
readings can stand in one clause:

```ruby
Light : [Low, High]

lift : [Low, Found(Nat)] -> Light
lift(Low) -> Low
lift(Found(_)) -> High
```

The pattern's `Low` is the row's tag, since the parameter is a row. The
body's `Low` is `Light`'s, since the result is a `Light`.

Where nothing decides, a word one declaration claims takes that declaration.
A word several declarations claim is an error:

```text
error: constructor `Failed` is ambiguous here
  = note: nothing decides between `Match.Failed` and `Parse.Failed`
  = help: qualify it, or let a signature decide
```

`Type.Ctor` names a constructor outright, in expressions and patterns:
`describe(Mode.Read) -> "read only"`. Inside a type's block, a bare word the
type declares always means its own constructor, and one that would resolve
to another type's is refused, with the qualified spelling as the fix.

## Constructor visibility

A module always sees its own constructors. Its export list decides what
importers see ([modules](../forms/modules.md)):

- `export {T}` publishes the type and its methods, and keeps construction
  and matching inside the module.
- `export {T.*}` publishes the constructors too, and an importer may then
  take one alone: `import std.host {Read}`.

A sealed type cannot be forged. Outside the module, `Email("x")` can only be
a structural tag, and no `Email` parameter takes one:

```text
expected `Email`, found `[Email(Str), *]`
```

Qualifying does not get around it: `Failure.NotFound` outside a module that
exported only `Failure` is refused as having no visible constructor.

## Data holds no functions

No payload, structural or nominal, may hold a function:

```text
Bad : [B((Nat -> Nat))]
error: constructor `B` holds a function
  = note: data may not store functions; a function is passed into a call
```

Why is under Rationale; what functions may do is
[functions](functions.md)'s.

## Rationale

### Why both nominal and structural tags?

They serve different things. Structural rows are for outcomes, the answers
that flow between functions, where a caller may join in a new failure
without anyone's permission and nobody asks whose `Missing` a value is. The
host's errors show it: `ReadError`, `WriteError` and `OpenError` are rows
holding only what each operation can meet, and `?` joins them where a
program uses several. Nominal types are for things: values with methods,
with laws the compiler checks against the block (a type with `cmp` takes its
`equals` from it), and, when the constructors are sealed, with a guarantee
such as `Str`'s valid UTF-8.

The cost is two kinds of identity to learn. A same-shaped structural value
never passes for a nominal one, which is the point of a seal but is also
what a newcomer trips on first. Reach for the structural form by default;
declare a type when it needs methods or laws, and seal it when it needs a
wall.

### Why resolve a tag by its position?

Because the information is already there, and numerals and methods already
resolve this way. A clause's parameter types and its result type say which
type each tag position wants before the word is read.

Ori first resolved by declaration: a declared constructor took its word
everywhere in the module. A module using `Absent` in structural scan rows
could not declare a type with an `Absent` case, and two types in a module
could not both have a `Failed`, so constructors wore their type's name,
`MatchFailed`, `ParsedAbsent`, on both sides of every clause. Faun's clap
library now declares `Failed` in both `Match` and `ParsedArg`, and shares
`Absent` with its scan rows. The cost is that a reader must know a
position's type to read its tag, and the one real ambiguity is reported
rather than guessed.

### Why does a word nothing decides take the declared reading?

Faun checks each definition once and specializes from the types checking
recorded, so an unsigned definition cannot be one type's constructor for
one caller and a row's tag for another. Ori deferred such a tag to each
caller as a bound; Faun does not. Taking the declared reading keeps an
unsigned definition's meaning the one a reader of the module would guess.

The cost is real: once `Light` declares `Low`, an unsigned `glow(_) -> Low`
answers a `Light`, and a caller wanting the row `[Low, Other]` is refused.
Declaring a type can therefore change what an unsigned definition below it
means. A signature on `glow` is the recourse.

### Why no written row tail?

Records have `{name: Str, *}`; variant rows have no `[Red, *]`, and the
grammar refuses one. The asymmetry follows how each is taken apart. A record
is read a field at a time, which never needs the whole row, so a type saying
"at least these fields" is useful. A variant is matched, and matching
covers the whole row, so "at least these tags" is a promise about a
catch-all clause, not a fact about the type. Each place a tail might serve
has an answer already:

- **Result position.** "These tags or more" is true at a caller joining
  producers, where inference says it, and false at a definition, which
  answers a known set.
- **Parameter position.** "I handle these and ignore the rest" is a
  catch-all clause's job.
- **A row mixed with a caller's.** Wrap it in a tag with a variable
  payload, `[TimedOut, Inner(e)]`, which records provenance instead of
  merging silently.

Some inferred types cannot be written. `_` in a signature covers the common
case, a failure row left to the `?`s.

### Why can exports hide constructors?

So a module can promise something about every value of a type. Only
`parse_email` builds an `Email`, so every `Email` was checked. Only the
target builds a `Host` or a `File`, so a program cannot forge authority or a
descriptor ([effects](../forms/effects.md)). Visibility does not reserve a
spelling: outside the module, the same word is just a structural tag that
no parameter of the sealed type accepts.

Why not mark visibility at the declaration? There are three named forms:
the transparent alias (`=`), the open nominal type (`:` with `T.*`) and the
sealed one (`:` with `T`). Two declaration operators cannot name three
things, and the export list is where a reader already looks for a module's
contract. The cost is that an importer cannot match a sealed type; it uses
the methods the module exports.

### Why can't data hold functions?

Faun's functions are second order. A definition taking a function is made
once for each set of callbacks it is handed, so every call of a parameter
is a direct call, and no closure exists at run time. A function stored in a
constructor would outlive the call that knows what it is, and would need
exactly the closures the language does without: a code pointer, captured
values and an indirect call.

Ori's reason was its totality checker: a recursive type holding a function
of itself lets a program recurse with no recursive call in sight. Faun does
not check termination, so that premise is gone; the representation reason
stands. The cost is that a table of handlers or a strategy cannot be data.
The recourse is data that says what to call. The rock-paper-scissors arena
holds its players as a sum, `Bot : [AlwaysRock(AlwaysRock), ...]`, each
constructor carrying a bot's state, and `Bot`'s methods forward to each
bot's own.

## Related

- [Records](records.md): the other row, read by field, with a written tail
- [Types](../types.md): inference, rows in general, and `where` bounds
- [Methods](../forms/methods.md): type blocks, derived members, and a sum's
  name standing for its constructors
- [Pattern matching](../forms/pattern-matching.md): coverage, which is what
  closes a row
- [Modules](../forms/modules.md): export lists and imports
- [Functions](functions.md): what a function may and may not be
