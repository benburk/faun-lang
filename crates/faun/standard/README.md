# Primary frontend standard library

`standard.fn` is the bootstrap package root. It exports `Bool`, `Order`, `Nat`,
`Int`, `U8`, `U16`, `U32`, `U64`, `F32`, `F64`, `List`, `Result`, `Str`,
`Hasher`, `Map`, `Mixer`, `Set`, `SortedMap` and `SortedSet` from sibling
modules.

A numeral takes its type from its position, as in Ori, and may be only a
`Nat`, `Int`, `U8`, `U16`, `U32` or `U64`; nothing else is made numeric by the
methods it defines. A word is built through its own `of_nat`, and its module's
private `numerals_below` bounds what may be written: `300` is not a `U8`,
though `U8.of_nat(300)` is 44. A numeral nothing types is a `Nat`, or an `Int`
when it is negated. The words are rings: they wrap by definition, and `sub`
is the ring's, not monus.

A numeral with a point, `1.5` or `1.0e-12`, is a float's, and only a float's:
`F32` or `F64` as its position decides, and `F64` where nothing does, built
through the float's `of_decimal(digits, scale)`, `digits / 10^scale`, and
negated through its `neg`. A numeral without one is never a float, so `3` is
not an `F64`; `3.0` is.

`F32` and `F64` are Ori's IEEE 754 binary32 and binary64 under `float/`,
ported whole: one core in `format.fn` that takes its format as a record, over
`U32` and `U64` patterns, computing each result exactly on naturals and
rounding it once, to nearest with ties to even. Every operation is total: an
invalid one answers the one NaN, and overflow an infinity. There are the
basic operations and `fma`, `sqrt`, the roundings to integers, conversions,
`to_str` and `from_str` that round-trip, `to_fixed`, `to_exponent` and
`to_precision`. `cmp` is the standard's total order, and `equals` follows it:
a NaN equals itself and `-0.0` is not `0.0`; `partial_cmp` and
`numeric_equals` are the hardware's. Ori's contract for them, rule by rule,
is `examples/floats/`.

Their `add`, `sub`, `mul`, `div` and `sqrt` are the one place the compiler
takes a meaning from a name: nothing an equation says makes a definition
IEEE 754's addition, so lowering tells Barb that these five, at each
float's own type, compute that operation (`Program::claim`). The
definitions stay, and answer wherever nothing faster does: on a target
without float instructions, and in a program the claims are taken from to
check them, as `examples/floats/` is asked both ways. Folding answers a
claimed call from its operands with the host's own arithmetic, and x86-64
with one SSE2 instruction; a NaN may then be any NaN's pattern, which no
program can tell, since `to_bits`, `cmp` and `sign_bit` read every NaN as
one. What is left in software -- `of_decimal`, the conversions and the
text -- costs a program that runs it thousands of instructions an
operation, and constant folding what it can a hundred thousand steps of
its budget: a numeral is folded, but slowly.

The words' `and`, `or` and `xor` reduce their answer modulo the word's
size. Two words' bits make a word, so the remainder changes nothing; it is
what shows range analysis the answer is one, since `Nat`'s bitwise walk is
recognized as nothing, and so what lets a `U64`, and an `F64` over it, be
held in a machine word rather than as a natural of any size.

`Nat.from_str` and `Int.from_str` read decimal text, `Err(Malformed)` where it
is not one: digits only, and for an `Int` a leading `-`. `Nat`, `Int` and `U8`
have `min` and `max`, and `U8` the ASCII tests `is_digit`, `is_ascii_lower`,
`is_ascii_upper` and `is_ascii_letter`, and `to_ascii_lower` and
`to_ascii_upper`.

`Str` is UTF-8 bytes behind a private wrapper, with `len`, `concat`, `cmp` in
byte order and `equals` from it, `from_ascii`, `from_utf8` and `to_utf8`.
`Bool`, the integers and `Str` say themselves with `to_str`, and a splice
`${value}` in a string is its value's `to_str`, the pieces joined with
`concat`. A string or character literal writes `\n`, `\r`, `\t`, `\0`,
`\\`, `\"`, `\'` and `\$` for themselves, and `\u{...}` for any scalar by
its one to six hexadecimal digits, as Rust does. For reading text there are `is_empty`, `split` at a separator,
`lines` at `\n` or `\r\n`, `trim` of ASCII white space, `starts_with`,
`ends_with`, `drop_prefix` and `drop_suffix`; for writing it,
`Str.join(pieces, separator)` and `repeat`. Matching and cutting go byte by
byte, which no character boundary can fall inside. There is no slicing by
position. A numeral pattern of a word and a string pattern are each a test
of equality, asked before the clause's guard.

`List` follows Ori's standard list: `len`, `is_empty`, `append`, `extend`,
`prepend`, `map`, `map2`, `flat_map`, `flatten`, `join`, `filter`, `count`,
`any`, `all`, `fold`, `fold_right`, `trail`, `reverse`, `first`, `last`,
`get`, `get_or`, `set`, `exchange`, `try_map`, `find`, `find_index`, `equals`,
`contains`, `sum`, `take`, `drop`, `take_while`, `drop_while`, `split_at`,
`partition`, `zip`, `unzip`, `cross`, `enumerate`, `windows`, `min`, `max`,
`sort`, `sort_on` and `to_str`, and the constructors `List.range(n)` and
`List.repeat(x, n)`. `sort` is a stable merge sort by the element's `cmp`, and
`sort_on` by a key's. `to_str` writes a list as it is written, `[1, 2, 3]`. A list
pattern's rest may go unnamed, as `[a, b, *]`. A
lookup that can miss answers a structural tag: `Err(OutOfBounds)`,
`Err(Empty)` or `Err(NotFound)`. Nothing is recognized by name: `len` is
answered from the length a list holds because Barb recognizes what it
computes.

## Tags

Tags follow Ori (`notes/values/tags.md` there). A capitalised word no visible
declaration claims is a structural tag: it belongs to no module and needs no
import, and rows of tags join by unification where values meet, so
`[NotFound, SomethingElse]` and `[Blah, NotFound]` flow into one
`[Blah, NotFound, SomethingElse]`. A row written in a signature is closed for
the body, which may answer only those tags, and open to callers, which may
join it with their own. A row in a parameter is what a definition handles
and stays closed. Clauses that take a row apart with no catch-all close it,
so a caller cannot hand them a tag no clause matches. A closed row answered
where a wider one is still being worked out joins it, as in Ori: a definition
answering `Bad(message)` in one clause and another's closed
`[Absent, Found(Nat)]` in the next answers all three, the closed value
rebuilt in the wider row where it is answered.

A word some visible declaration also claims is read as its position's type
decides: a tag row takes the tag, a nominal type its constructor, and a
position nothing decides the one declared reading, or an ambiguity error
where several types declare the word. `Type.Ctor` names a constructor
outright, in expressions and patterns. Inside a type's block, a bare word the
type declares means its own constructor. `exports {T}` keeps `T`'s
constructors private, and a same-spelled structural tag never becomes one.
`exports {T.*}` makes them public, and an importer may then select one by
itself, as Ori does: `import std.host {Read}` binds that constructor alone.

Faun specializes from the types checking recorded rather than inferring each
specialization again, so where a closed row is answered as a signature's
wider one, a caller's, the value is rebuilt in the wider row. Tag rows have
no written tail, as in Ori; a tag used as a function value is not here yet.

A closed row has `equals` and `to_str` without declaring them, as in Ori:
two values are equal where they are one tag with equal fields, and a tag is
written as its name, and its fields after it by their own `to_str`,
`Invalid(3)`. A row a caller may still add tags to has neither. `Result`
writes its own `equals`, both sides by their types' own, so
`Nat.from_str(text) == Ok(48)` asks it of a `Nat` and a row.

A closed record and a tuple have `equals`, `to_str` and `hash_into` the same
way, and a tuple `cmp` too. A record is written with its fields in the order
of their names, `{x: 1, y: 2}` however it was written, and a tuple with its
members in order, `(1, a)`. A record with `*` has none of them: its other
fields are a caller's.

`value?` is an `Ok`'s value, or its `Err` answered at once by the clause or
lambda it is written in, which answers a `Result`. Each `?` adds its
producer's failure tags to that answer's row, so failures from several
producers join without an umbrella type, and a signature's row admits only
its own.

A signature may write `_` for any part of a type it leaves to the clauses:
`app : {stdin: List(U8), *} -> Result(Nat, _)` holds what it writes, and its
failure row is whatever its `?`s join, reported by the row's own `to_str`.
Such a definition is worked out as an unsigned one is, from the type written
rather than from nothing, so it takes no `where` bounds. `_` stands for a
type nowhere else: a data declaration or an alias says its type in full.

```sh
cargo run -- check crates/faun/examples/utilities.fn
cargo run -- emit --target x86_64-linux barb crates/faun/examples/main.fn
```

A key says what it is made of through `hash_into : (T, h) -> h`, generic over
any hasher: `Hasher(h)` is the alias for a type with `write_u64` and
`write_bytes`, and nothing more, so a key can feed a hasher but never read a
digest out. The numbers, `Bool`, `Str` and `List` define it; a tuple or a
closed record has its own, feeding its members in order. `Map` and `Set`
feed the library's own `Mixer` (`mixer.fn`) and keep their entries in
insertion order, so no program observes the mixing. The package exports
`Mixer` as a type alone, for a generic signature over a map to bound its
key by `k.hash_into : (k, Mixer) -> Mixer`; neither its seed nor its digest
is exported. `SortedMap` and `SortedSet` are AVL trees ordered by the key's
`cmp`, for keys that must come back in order. `List.group_by` gathers into a
`Map`.

The package has no bodyless derivation: a declared type's `equals`, `cmp`
or `hash_into` is written out, as `Map`'s `Slot` writes its `equals`.

Generic code that uses a method has a `where` bound, as in Ori: structural,
met by any type having the member, with no trait and no runtime dictionary.
A signature writes them after `where`, each member on a line of its own:
`sum : List(a) -> a where` over `a.zero : a` and `a.add : (a, a) -> a`, a
value member called on the type as `a.zero()`; an unsigned definition
infers them, so `double(x) -> x.mul(2)` serves every type with a `mul`. Where
every method a generic receiver could have shares a shape, that shape is
context before any default, so the `2` is whatever `x` is, built through its
type's `of_nat`. Each specialization calls the concrete type's own member.
A bound may mention a variable the signature does not, and another bound may be
on it: in `r.fold : (r, Nat, (Nat, x) -> Nat) -> Nat` with `x.name : x -> Str`, `x`
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

Records are structural and unordered. `{name: Str, *}` is a record with at
least a `name`, and reading `.name` asks exactly that of whatever record it
is given. On a receiver nothing has typed yet, `.name` without parentheses is
such a read, as in Ori, and never a guess at a method of that name; `{x, *}` in a pattern names some fields and takes the rest;
`{x: e, *r}` is `r` with `x` replaced, and adds or retypes nothing. A tuple
A record literal handed alone to a function whose signature pairs two values of
one shape, `(F(a, e), F(b, e), (a, b) -> c) -> F(c, e)`, is that function
applied a field at a time, as Ori's record builders are: `both({x: rx, y: ry,
z: rz})` pairs `rx` and `ry` into `{x, y}`, then that with `rz` into the whole
record, each field evaluated once in the order written. The signature's shape
asks for it, never the function's name.

`(a, b)` is a positional product of two or more, built by its literal and
taken apart by a pattern, and never unifies with a record. A binding may
take a record or tuple apart, since that always matches, and a type's one
constructor. A closed record and a
tuple have `equals` without declaring it, as a tag row does, each component
equal by its own type's `equals`, and a tuple has `cmp`, its positions in
order with `Order.then`;
a record has no order of its fields, and an open record no `equals`, its other
fields being a caller's. A declared type writes its own.

`&`, `|` and `^` are `and`, `or` and `xor`, as in Ori: logical on `Bool` and
bitwise on `Nat` and the words, and looser than a comparison, so
`x == 3 & y == 5` needs no parentheses and `(a & b) == 8` does. The words
also have `zero`, and `bit_not`, `shift_left`, `shift_right`, `rotate_left` and
`rotate_right`, each by a `Nat` count of bits; a shift by the width or more
is nought. `Int` has no bitwise operations.

`Nat`, `Int`, and `U8` define `+`, `-`, `*`, `/`, and `%`. A type is ordered by
defining one `cmp : (T, T) -> Order`, and `<`, `<=`, `>` and `>=` are fixed views of
its `Order`, so they cannot disagree; `Bool`, `Nat`, `Int` and `U8` define it. Natural subtraction is
monus. Signed division is Euclidean, as Ori's is: the remainder is never negative,
so `-7 / 3` is `-3` and `-7 % 3` is `2`. For every type, division by zero returns zero and `a % 0` returns `a`.
`U8` arithmetic uses unsigned representatives and wraps modulo 256; in particular,
`0 - 1` is 255 rather than natural zero.

The structural empty variant type `[]` is the uninhabited result used by
applications; it needs no blessed standard-library name. `Never` remains an
ordinary available constructor spelling. Each target has its own host module,
`hosts/<target>.fn`, mounted at `std.host`. They start out identical and will
diverge as targets offer different capabilities. Each declares Ori's host
streams:

```
Host : {args: List(Str)}.(
  exit! : (Host, Nat) -> []
  stdin : Host -> Stdin
  stdout : Host -> Stdout
  stderr : Host -> Stderr
  files : Host -> Files
)

Stdin    read! : (Stdin, Nat) -> Result(List(U8), IoError)
         read_to_end! : Stdin -> Result(List(U8), [Io(IoError), LimitExceeded])
         read_to_str! : Stdin -> Result(Str, [Io(IoError), LimitExceeded, InvalidUtf8])
Stdout   write!, write_all! : (Stdout, List(U8)) -> Result(Nat, IoError)
Stderr   write!, write_all! : (Stderr, List(U8)) -> Result(Nat, IoError)
Files    open! : (Files, Str, Mode) -> Result(File, IoError)
File     read!, read_to_end!, read_to_str!, write!, write_all!, as the streams
         close! : File -> Result(Nat, IoError)
Mode     [Read, Overwrite, Append, CreateNew, Edit, Load]
```

with `IoError` the tags `NotFound`, `Denied`, `AlreadyExists`, `NotADirectory`,
`IsADirectory`, `NotEmpty`, `Escapes`, `BrokenPipe`, `NoSpace`, `Unsupported`
and `Other(Nat)`, each
host reading its own error numbers into them. A `read!` or `write!` moves some
bytes, at most 64 KiB read at once (1 KiB on sim65), and answers how many; `read_to_end!` and
`write_all!` are Faun in the host module, going on until the stream is done,
each bounded by fuel so it is seen to stop. The `Host`, `Stdin`, `Stdout`,
`Stderr`, `Files` and `File` constructors remain private, so only the target
makes one. A method of a value's own type is reached whether or not the type
was imported, so `host.stdout.write_all!(bytes)` needs only `Host`. A method a
type's block writes without a signature is one all the same, called with a dot
from anywhere its type reaches; its type is inferred before its callers'.

Every stream is what a descriptor names, the standard three first, and a
target answers for four routines over descriptors: bytes written, bytes read,
a name opened, and a descriptor closed. Bytes cross where they lie: a write
hands the target the list's own bytes, and a read fills a new list the target
is handed room in, so nothing is copied on the way. Each answers a number, or an error as a kernel does, that
far short of the top of a word; the host module's `outcome` tells which, so
nothing is kept between one call and the next.

`Files.open!` finds a name beneath where the program runs and nowhere else: a
name reaching above it, by `..`, from the root or through a link, is refused as
`Escapes` where the target can tell, and as `Denied` under WASI. sim65 opens
whatever it is handed, so its host module refuses a name from the root or
holding a `..` itself, and cannot see a link. A name holds no nought byte; where the kernel reads a
name up to one, the host module appends one, in place where the name's buffer
has room and nothing else holds it. How long a name may be is the target's to
say: Linux and a WASI host refuse one too long themselves, and sim65, which
would copy a longer one past its own 1024 bytes, is never handed one over
1023.

A `File` is a resource: whatever opens one must use it up exactly once on
every way it goes on, by closing it or answering it to something that does.
Dropping one, using one after it is closed, and leaving by `?` while one is
held are each refused where the program is checked. `?` closes nothing, so a
file is closed before `?` is asked of what reading or writing it answered:

```
source = files.open!("input.txt", Read)?
reading = source.read!(4096)
closing = source.close!()
contents = reading?
closed = closing?
```

Nothing is written to say what a function does with a file it is handed:
one that only reads, writes, or hands it on to what does the same lends it,
and its caller still holds it; one that closes or answers it on every way it
goes on takes it. A function that does one on some ways and the other on
others is refused. What makes a type a resource is a routine the target
declares as using up what it is handed, here closing a descriptor; a type
holding a resource, such as `List(File)` or `Result(File, IoError)`, holds one
too.

`host.print!(text)` and `host.println!(text)` write a text to standard output,
the second with a line's end, and answer `Result({}, IoError)`. An effect whose
answer nothing needs is written on a line of its own, which binds it to `_`.
Only an effect, a call of a name ending `!`, may stand so; anything else is
bound to a name:

```
main!(host) ->
  host.println!("Hello, world!")
  host.exit!(0)
```

A line beginning with an infix operator, or with a `.`, goes on with the
line before rather than standing on its own, so a long condition may be
broken before its `&`. A `-` held to what follows it is a negation and
begins a line of its own.

## Or-patterns

`A | B` among a clause's parameters matches either alternative, and every
alternative binds the same names at the same types. A clause holding one is
a row for each choice of alternatives, checked and covered as those rows
would be. A binding's or a lambda's pattern must match whatever it is
handed, and holds none: names, records, tuples, and the constructor of a
type that has no other, as in `(value, Memo(entries)) = step(n)`. A binding may shadow a name already in scope, as in Ori: its value reads
the name as it was, and every line after reads the nearest, so
`v = v + 1` counts on. A binding's or a lambda's pattern binds each name once.

A clause's head may bind a name twice, and then matches only where both are
equal by their type's `equals`: `doubled([a, a]) -> True` is
`doubled([a, b]) if a == b -> True`, the equality asked before any guard
written. The clause covers only equal values, so another must cover the
rest, and an alternative of `|` binds each name once, since the equality is
asked of the whole clause.

```
bucket : Nat -> Nat
bucket(0) -> 0
bucket(1 | 2) -> 1
bucket(_) -> 2
```

## Ranges

A range pattern, `lo..hi` of numerals or characters, is inclusive at both
ends and follows Ori (`notes/forms/pattern-matching.md` there). Either end
may be negative, `-10..-1`, or `_`, leaving that side open: `_..-1` and
`0x80.._`; `_.._` is refused as the wildcard it would be. A range binds
nothing, and is a test of the value's `cmp` at each end it has, asked with the
clause's other literal tests before its guard. A clause holding one is
guarded, so it covers nothing, and a group of them ends in a clause without.
A reversed range, which could match nothing, is refused. Unlike Ori's, a
range may stand in an or-pattern's alternative, since each alternative is a
row of its own, as a word's numeral already may.

```
utf8([0xe0 0xa0..0xbf 0x80..0xbf *rest]) -> utf8(rest)
is_digit(U8('0'..'9')) -> True
is_digit(_) -> False
sign(_..-1) -> Negative
```

## Callbacks

A function is passed straight into a call and never held, so what each
function parameter is, is known where it is passed. A definition taking a
function is made once for each set of callbacks it is handed, as in Ori, and
calling its parameter is a direct call of the callback; a lambda is a
definition of its own, handed what it reads from where it was written. Each
callback's calls are then seen to stop as they would on their own:
`bytes.count(|byte| ['a', 'e'].contains(byte))` goes round only as `contains`
does. A recursive call that wraps the callback it was handed in a new lambda
each time round is refused, since it would need a definition for every
round; recurse on data that says what to call instead.

## Packages

A package is its root module's directory and every module it imports from
there. Its root may name the packages it depends on in its header, each a
module base relative to the header's file, as Ori's `app {}` and `lib {}` do:

```
package {
  md5: "../libraries/md5/src/md5"
}

import md5 {md5_hash}
```

Any module of the package may then import `md5`, which is that package's
root module; its inner modules are its own, and importing one is refused. A
dependency's modules resolve their imports from its root, with its own
header's dependencies. Only a package's root module has a header. Whether a
package is an application is whether its entry defines `main!`.

## Expectations

`expect` followed by a body is a claim a module makes of its definitions:
a clause of no parameters answering a `Bool`, bindings allowed, as in Ori.

```
double : Nat -> Nat
double(n) -> n * 2

expect double(2) == 4
expect
  doubled = [1 2 3].map(double)
  doubled.len() == 3
    & doubled.last().ok_or(0) == 6
```

An expectation is checked as any definition is, typed, exhaustive and seen to
stop, whenever its package is. No program can name one. `faun test PATH`
builds the package at `PATH` with an entry of its own in place of any `main!`,
which is checked all the same: the entry asks every expectation of every module in the package, those of the
standard library and of packages it depends on aside, and prints the number
of each that does not hold.
The standard library is a package too, and holds expectations of its own:
`faun test crates/faun/standard/standard.fn` asks them.
`faun test` runs that for the machine it is on and says where each failing
expectation was written; what the compiler settled while compiling, it
settled before the program ran.

`Host` also has two runners, the quick way to a whole program: `run!` hands
a pure function `{args: List(Str)}`, and `run_stdin!` reads standard input to
its end first and hands `{args: List(Str), stdin: List(U8)}`: the bytes as
they came, so a program hashing or decoding them pays for no text check, and
one wanting text asks `Str.from_utf8` itself. Each prints what the function
answers by its `to_str` and a line's end, and finishes with status nought. A
function declares the fields it reads, `{stdin: List(U8), *}` taking the
input and leaving the arguments; one answering a `Result` prints `Ok(...)` or
`Err(...)`, which says which it was. So `main!(host) -> host.run_stdin!(app)`
is a whole program, and one that must finish with another status writes its
own `main!` and calls `exit!`. Only the host failing finishes otherwise: the
answer not written, or input that cannot be read.

A target answers for smaller primitives than these: moving a run of bytes that
lie in memory, answering how many or `-errno`. Machine lowering builds each
stream routine on its primitive through a scratch region of one run, and keeps
the last error for the host module to ask after. What a routine answers as a
byte string is known to be bytes wherever a program reads them.

An entry's `main!` is `Host -> []`, whether or not it says so: one written
without a signature is given that one, so its `host` is a `Host` from the
start and what it asks of it is found on `Host` without importing it.

`Host` is authority carrying what its target hands the program: `host.args`,
the arguments it was run with, its own name first, read like any record
field. `host.args.len()` is how many there are, and
`host.args.get_or(1, "world")` the first after its name. In Barb, `Host` holds
its fields itself, `Host(args: List<Str>)`, and `main!` is the entry as
written. A target hands the entry the arguments as C lays them out, a count
and where their addresses lie, as its startup table says; machine lowering
makes them the list of strings where the entry begins, once, and only for a
program that reads them. One that reads only how many there are is handed the
count alone and makes no list, and one that reads neither is handed nothing.

`Host`'s bodyless methods are the effects the target answers for, called as
`host.stdout.write_all!(bytes)`. A program orders its effects by threading `Host` through
them. Barb calls each routine with the `Host` it was handed, as the source
says, and keeps the order and number of calls to anything bodyless. A routine
asked with authority reads nothing of it, so machine lowering hands nothing
for it, and passing `Host` along is not reading what it carries: a program
that never reads `host.args` makes its target produce nothing.
