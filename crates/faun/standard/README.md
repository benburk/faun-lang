# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Order`, `Nat`,
`Int`, `U8`, `U16`, `U32`, `U64`, `List`, `Result`, and `Str` from sibling modules.

A numeral takes its type from its position, as in Ori, and may be only a
`Nat`, `Int`, `U8`, `U16`, `U32` or `U64`; nothing else is made numeric by the
methods it defines. A word is built through its own `of_nat`, and its module's
private `numerals_below` bounds what may be written: `300` is not a `U8`,
though `U8.of_nat(300)` is 44. A numeral nothing types is a `Nat`, or an `Int`
when it is negated. The words are rings: they wrap by definition, and `sub`
is the ring's, not monus.

`Str` is UTF-8 bytes behind a private wrapper, with `len`, `concat`, `cmp` in
byte order and `equals` from it, and `from_ascii`. `Bool`, the integers and
`Str` say themselves with `to_str`, and a splice `${value}` in a string is its
value's `to_str`, the pieces joined with `concat`. Numeral patterns on words
and string patterns are not here yet.

`List` follows Ori's standard list: `len`, `is_empty`, `append`, `extend`,
`prepend`, `map`, `map2`, `flat_map`, `flatten`, `join`, `filter`, `count`,
`any`, `all`, `fold`, `fold_right`, `trail`, `reverse`, `first`, `last`,
`get`, `get_or`, `set`, `exchange`, `try_map`, `find`, `find_index`, `equals`,
`contains`, `sum`, `take`, `drop`, `take_while`,
`drop_while`, and the constructors `List.range(n)` and `List.repeat(x n)`. A
lookup that can miss answers a structural tag: `Err(OutOfBounds)`,
`Err(Empty)` or `Err(NotFound)`. Nothing is recognized by name: `len` is
answered from the length a list holds because Barb recognizes what it
computes.

## Tags

Tags follow Ori (`notes/values/tags.md` there). A capitalised word no visible
declaration claims is a structural tag: it belongs to no module and needs no
import, and rows of tags join by unification where values meet, so
`[NotFound SomethingElse]` and `[Blah NotFound]` flow into one
`[Blah NotFound SomethingElse]`. A row written in a signature is closed for
the body, which may answer only those tags, and open to callers, which may
join it with their own. A row in a parameter is what a definition handles
and stays closed. Clauses that take a row apart with no catch-all close it,
so a caller cannot hand them a tag no clause matches.

A word some visible declaration also claims is read as its position's type
decides: a tag row takes the tag, a nominal type its constructor, and a
position nothing decides the one declared reading, or an ambiguity error
where several types declare the word. `Type.Ctor` names a constructor
outright, in expressions and patterns. Inside a type's block, a bare word the
type declares means its own constructor. `exports {T}` keeps `T`'s
constructors private, and a same-spelled structural tag never becomes one.

Faun specializes from the types checking recorded rather than inferring each
specialization again, so where a closed row is answered as a signature's
wider one, a caller's, the value is rebuilt in the wider row. Tag rows have
no written tail, as in Ori; a tag used as a function value and a row's
automatic `to_str` are not here yet.

`value?` is an `Ok`'s value, or its `Err` answered at once by the clause or
lambda it is written in, which answers a `Result`. Each `?` adds its
producer's failure tags to that answer's row, so failures from several
producers join without an umbrella type, and a signature's row admits only
its own.

```sh
cargo run -- check crates/faun/examples/utilities.fn
cargo run -- emit --target x86_64-linux barb crates/faun/examples/main.fn
```

The package deliberately omits hashing and bodyless derivation.

Generic code that uses a method has a `where` bound, as in Ori: structural,
met by any type having the member, with no trait and no runtime dictionary.
A signature writes them, `sum : List(a) -> a where a.zero : a a.add : a a -> a`,
a value member called on the type as `a.zero()`; an unsigned definition
infers them, so `double(x) -> x.mul(2)` serves every type with a `mul`. Where
every method a generic receiver could have shares a shape, that shape is
context before any default, so the `2` is whatever `x` is, built through its
type's `of_nat`. Each specialization calls the concrete type's own member.
A bound may mention a variable the signature does not, and another bound may be
on it: in `r.fold : r Nat (Nat x -> Nat) -> Nat` with `x.name : x -> Str`, `x`
is whatever `r`'s `fold` hands over, which `r`'s implementation says at each
specialization. A bound on a variable neither the signature nor such a bound
reaches is refused, and one whose types no implementation determines is refused
where it is used rather than guessed.
`Name(a) = where ...` names requirements that a `where` clause applies
together as `Name(a)`. An alias is no type and has no implementation: it
expands where it is applied, and composes, exports and imports as a type name
does. A variable its body names besides its parameters is its own, apart from
the clause's; a member required twice alike is required once, and twice
differently is refused, as is an alias that applies itself.

Records are structural and unordered. `{name: Str *}` is a record with at
least a `name`, and reading `.name` asks exactly that of whatever record it
is given; `{x *}` in a pattern names some fields and takes the rest;
`{x: e *r}` is `r` with `x` replaced, and adds or retypes nothing. A tuple
`(a b)` is a positional product of two or more, built by its literal and
taken apart by a pattern, and never unifies with a record. A binding may
take a record or tuple apart, since that always matches. A closed record and a
tuple have `equals` without declaring it, each component equal by its own
type's `equals`, and a tuple has `cmp`, its positions in order with `Order.then`;
a record has no order of its fields, and an open record no `equals`, its other
fields being a caller's. A declared type writes its own.

`Nat`, `Int`, and `U8` define `+`, `-`, `*`, `/`, and `%`. A type is ordered by
defining one `cmp : T T -> Order`, and `<`, `<=`, `>` and `>=` are fixed views of
its `Order`, so they cannot disagree; `Bool`, `Nat`, `Int` and `U8` define it. Natural subtraction is
monus. Signed division truncates toward zero and its remainder has the dividend's
sign. For every type, division by zero returns zero and `a % 0` returns `a`.
`U8` arithmetic uses unsigned representatives and wraps modulo 256; in particular,
`0 - 1` is 255 rather than natural zero.

The structural empty variant type `[]` is the uninhabited result used by
applications; it needs no blessed standard-library name. `Never` remains an
ordinary available constructor spelling. Each target has its own host module,
`hosts/<target>.fn`, mounted at `std.host`. They start out identical and will
diverge as targets offer different capabilities. Each declares Ori's host
streams:

```
Host : {argc: Nat}.(
  exit! : Host Nat -> []
  stdin : Host -> Stdin
  stdout : Host -> Stdout
  stderr : Host -> Stderr
)

Stdin    read! : Stdin Nat -> Result(List(U8) IoError)
         read_to_end! : Stdin -> Result(List(U8) [Io(IoError) LimitExceeded])
         read_to_str! : Stdin -> Result(Str [Io(IoError) LimitExceeded InvalidUtf8])
Stdout   write!, write_all! : Stdout List(U8) -> Result(Nat IoError)
Stderr   write!, write_all! : Stderr List(U8) -> Result(Nat IoError)
```

with `IoError` the tags `NotFound Denied AlreadyExists NotADirectory
IsADirectory NotEmpty Escapes BrokenPipe NoSpace Unsupported Other(Nat)`, each
host reading its own error numbers into them. A `read!` or `write!` moves some
bytes, a run of at most 256, and answers how many; `read_to_end!` and
`write_all!` are Faun in the host module, going on until the stream is done,
each bounded by fuel so it is seen to stop. The `Host`, `Stdin`, `Stdout` and
`Stderr` constructors remain private, so only the target makes one. A method
of a value's own type is reached whether or not the type was imported, so
`host.stdout.write_all!(bytes)` needs only `Host`.

`Host` also has Ori's runners, which finish the program for it: `print!`
writes a text; `run!` and `run_text!` run a pure function of nothing or of
`{stdin: Str}` and print what it answers; `run_result!` and
`run_result_text!` do the same for one answering a `Result`, reporting an
error on standard error as `error: ...`. Each finishes with status nought, or
one where something went wrong, so `main!(host) -> host.run_text!(app)` is a
whole program.

A target answers for smaller primitives than these: moving a run of bytes that
lie in memory, answering how many or `-errno`. Machine lowering builds each
stream routine on its primitive through a scratch region of one run, and keeps
the last error for the host module to ask after. What a routine answers as a
byte string is known to be bytes wherever a program reads them.

`Host` is authority carrying the startup values its target produces. A field
such as `host.argc` is read like any record field; the target produces it into
the entry's frame before `main!` runs, and nothing asks for it again. In Barb,
`Host` holds its fields itself, `Host(argc: Nat)`, and `main!` is the entry as
written; nothing there says how wide `argc` is. Machine lowering recognizes a
field named for one of the target's startup values, holds it as the target's
startup table says, names the entry's parameter for it, and drops the ones
nothing reads, so a target produces only the startup values a program uses. A
read field the target cannot produce is refused by the target.

`Host`'s bodyless methods are the effects the target answers for, called as
`host.stdout.write_all!(bytes)`. A program orders its effects by threading `Host` through
them. Barb calls each routine with the `Host` it was handed, as the source
says, and keeps the order and number of calls to anything bodyless. A routine
asked with authority reads nothing of it, so machine lowering hands nothing
for it, and passing `Host` along is not reading what it carries: a program
that never reads `host.argc` makes its target produce nothing.
