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
   built.
7. **First element.** A list read only for its first element, such as a
   search, stops once it has it.
8. **In place.** A walk rebuilding a list element for element becomes
   indexed replacements, which lowering can do in place on an unshared
   buffer.

Fold what is known:

9. **Simplification.** Callee-first constant folding, identities, and
   sharing repeated calls, so a caller sees its callees' answers.
10. **Specialization.** Copy a loop for each known value its callers pass,
    where that decides a match, then simplify again.
11. **Joining rounds.** Inline again where specializing left two
    definitions calling each other, so the loop calls itself.

Tidy up:

12. **Sweep.** Drop definitions the entry doesn't reach.
13. **Cleanup.** Drop unused pure work, move work into the one arm that
    reads it, and compact the term arena.

Pure work can be dropped or moved freely. Calls reaching a declaration are
effects and keep their order, count and path.
