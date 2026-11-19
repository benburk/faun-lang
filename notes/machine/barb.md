# Barb

Barb is Faun's main IR. It sits where GHC's Core does, between the frontend
and machine lowering, but it is smaller: first-order, monomorphic, and in
A-normal form, with no lambdas, type abstraction or laziness. Five
expression kinds:

```
body = let x = expr ...; expr
expr = x                                   a local
     | C(x...)                             a construction
     | static k                            a known value
     | f(x...)                             a call
     | match x { C(x...) => body, ... }    one arm per constructor
```

- Locals are immutable de Bruijn levels.
- Calls and constructions are saturated.
- Arguments and match scrutinees are locals.
- Constructor fields become the next locals in an arm.
- A function has a body, or only a declaration that the target implements.
  Effects are declarations.
- Programs reaching Barb are well-typed and exhaustive. They need not stop.

Barb keeps the high-level shape of a program: types are still constructors,
loops are still recursion, a list is still a list. That is what makes
patterns easy to find. The [README](../../crates/core/src/barb/README.md) is
the full contract.

## Nothing is blessed, only recognized

Barb has no built-in integers, lists or strings. A number is recursion over
constructors, and `Bool` is a two-constructor type like any other. Barb
finds what a definition computes from its equations, never its name, and
records it as a fact:

- arithmetic: add, multiply, monus, divide, modulo, bitwise and/or/xor,
  power, rotation
- sequences: length, reverse-onto, prepend, append, drop, take, replace
- floats: add, subtract, multiply, divide, square root, comparison

A recognized definition keeps its body. The body is the meaning; the fact
lets later passes fold the call and lets a target use one instruction for
it. A target without the instruction walks the body.

Floats are recognized by their code. No equation shows that a routine
walking bits rounds as IEEE 754 does, so Barb doesn't try. It knows the
standard's float routines by fingerprint: a hash of a definition's code and
everything it calls, after canonicalizing, with no names in it. If a
definition's code is the standard's `add`, it is IEEE add. The frontend
says nothing, and `just bless` rewrites the table when the standard
changes.

So the frontend API is just the program: types, functions, the entry, and
which declarations the target provides.

Every program has exactly one entry, and every optimization is rooted
there: what it doesn't reach is dropped, and only its parameters come from
outside. A library has no entry, so it stops at the frontend's checks and
never becomes Barb.

## Facts about data

Barb classifies each type's shape: unit, wrapper, product, natural,
sequence, enumeration, general sum, and so on. With that it derives value
ranges, sequence lengths, small affine summaries, and purity.

Barb does not choose representations. Machine IR does, using these facts
and the target's capabilities: a natural known to fit 8 bits is a byte, a
sequence is a buffer, a product is flattened into its fields. A program
can't observe which it got.

## Passes and facts

A pass takes a Program and rewrites it in place. The output is always plain
Barb.

Facts are not handed from pass to pass. A pass asks for them when it needs
them, and `program.analyze()` derives them from the program as it stands.
Only recognition is cached on the Program, because rewriting a body keeps
what it means. Expression IDs change on rewriting, so facts attach to
functions, types and fields where they can. Reanalyze after optimizing.

Barb handles what it can prove at its level: list identities and fusion,
recognized arithmetic, known values, lengths and ranges. Storage reuse,
reference counts and word widths belong to machine IR. Instructions and
registers belong to the target.

## The schedule

`optimize` runs a fixed list of stages once, in this order. There are no
switches.

Shape the program:

1. **Canonicalization.** Substitute aliases, take records apart once, and
   take decided matches, in every body before recognition and again after
   it. Recognition sees code as it comes to, not as the frontend wrote it,
   and inlining prices helpers fairly.
2. **Building forward.** A walk like `map` builds its list front to back,
   so its recursive calls are tail calls.
3. **Descent.** A definition taking two numbers down together becomes its
   base cases on their differences, so it stops recursing.
4. **Constants.** A definition taking nothing that does work is folded
   where the budget allows, left alone where it is named once in a
   definition made at most once, so inlining can fuse it with its reader,
   and otherwise worked out once in the entry and handed to every
   definition reaching it as a parameter. A walk naming a table then reads
   it rather than building it every round
   ([computation](../computation.md#a-constant-is-worked-out-once)).
5. **Inlining.** Copy helpers into their callers, keeping one loop breaker
   per cycle. Mutual recursion becomes self-recursion. Arithmetic
   identities apply here too.

Remove list work:

6. **Fusion.** A list built by one walk and read once by another is never
   built. The building walk may walk a number down rather than a list, as
   `List.range` does, and may push one value every round from either end,
   as `List.repeat` does; a chain written inside a fused walk's step, as a
   recursion through `map` writes one, is fused there too. So
   `List.range(n).fold(...)` is one loop counting up.
7. **First element.** A list read only for its first element, such as a
   search, stops once it has it.
8. **In place.** A walk rebuilding a list element for element becomes
   indexed replacements, which lowering can do in place on an unshared
   buffer.

Fold what is known:

9. **Simplification.** Callee-first constant folding, identities, and
   sharing repeated calls, so a caller sees its callees' answers.
   Then a list a counting walk builds, `List.range(n).map(f)`, handed to a
   definition reading it only by its length and by what dropping a
   position leaves, goes to a copy taking what the walk was handed: the
   length is the count, and position `i` holds `f` worked out at `i` where
   `i` is below it, and nothing where it is not, as the list built does.
10. **Specialization.** A construction nothing but one call reads, handed
    to a definition that takes it apart, goes to a copy of the definition
    taking its fields, where simplifying the copy decides a match: so
    `key == [grey]` compares without building `[grey]`. Then copy a loop
    for each known value its callers pass, where that decides a match, and
    simplify again.
11. **Joining rounds.** Inline again where specializing left two
    definitions calling each other, so the loop calls itself.

Tidy up:

12. **Sweep.** Drop definitions the entry doesn't reach.
13. **Cleanup.** Drop unused pure work, move work into the one arm that
    reads it, work a pure read of a list out before an earlier write of it,
    so the write can be in place, and compact the term arena.

Pure work can be dropped or moved freely. Calls reaching a declaration are
effects and keep their order, count and path.

## Rationale

### Why is a range built front to back?

`List.range(n)` was built from the end, `range_into(n, [])` pushing each
count left in front, and fusion reads only a walk handing elements in the
order a reader takes them. Built front to back, an element for each step
down what is left, `range` is a producer like `map`, and a fold reading it
reads each element as it is made. Its elements are still bounded by
`count`: a count kept beside a walk down what is left never passes what
the two start as together
([counters](../../crates/core/src/barb/counters.rs)).

`List.repeat` was left building from the end. Front to back, evaluating
a known repeat at compile time appends to a list a walk at a time, which
cost a third more compiling for inflate's table of noughts; and a walk
pushing the same value every round builds the same list from either end,
so fusion takes it as it is.

### Why work out an element where it is read?

A list read by position, `xs.get(i)` walking `i` up to `xs.len()`, held
every element at once to read each one once: on x86-64 nine times the
memory of the same sum written as a fold, which fusion never builds. Its
copy reads no list. An element is worked out where it would have been
read, and never more often than building the list worked it out: the
reader must read one position a step, a position it counts up by a known
number each time it goes round, or one position at most without going
round, and the list must be read by that one call alone. So a table built
once and looked up many times, `crc32`'s, is built as it was; and a list
read at a position not counted up, read from its end, or handed to
anything else as well is built.

### Why copy a definition for a construction rather than inline it?

`equals` calls itself, so inlining stops at it, and a recursion over a
list is what most definitions taking a list apart are. A copy taking the
construction's fields is what inlining one round would leave, with the
rest of the recursion still the original's. Each copy's own calls are read
again, so a literal of three elements takes three copies, one for each
element, and the last hands on the known empty end.

The cost is size. A copy is kept only where it decides a match, only for a
body that may run more than once, since one run once builds its
construction once, and only where a copy for each constructor of the
construction copies no more than inlining copies of one callee. md5's
four-word digest flattened through `flat_map` would take four copies of a
walk for a list built once; it takes none.

### Why not recognize `range` or `==` by name?

Barb recognizes by shape. A program's own walk counting a number down
while building front to back fuses as `range` does, and its own
comparison of a list it builds is taken apart as `equals` is.

## History

- **2026-11-19:** a list a counting walk builds, read only by position
  and length, is never built. `walk-index` holds 32 KiB on x86-64 where
  it held 300, and runs 4.6 million instructions where it ran 14.7.

- **2026-11-17:** a range or a repeat read once by a fold, a `map` or a
  `filter` is never built, and neither is a list literal only compared.
  Queens, whose range is filtered and mapped through recursion, runs 27%
  fewer instructions on x86-64, 23% fewer cycles on the 6502, and is 16%
  smaller; a 1024 by 1024 interlaced PNG decoded through
  `List.range(width).fold` and `key == [grey]` takes 2.37 billion
  instructions rather than 3.75, within 6% of the decoder written as
  recursion and a match.
