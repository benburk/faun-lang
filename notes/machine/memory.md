# Memory

This note owns how Faun's immutable values live in memory: reference
counting, where counts are taken and given up, writing in place where
nothing else holds a value, the copy made where something does, and why no
value can hold itself. All of it happens in the machine tier, below
anything a program can see; the tiers are described in
[architecture](architecture.md).

## What is counted

Machine IR holds each value in one of a few classes, and three of them
carry a reference count:

- **Cells,** a sum with fields or a product too wide to hold flat. A cell
  is immutable once built.
- **Sequence buffers,** which hold a `List` or a `Str`: a buffer, where in
  it the sequence starts, and its length. A tail is the same buffer from
  one element on, so taking a list apart copies nothing.
- **Naturals** too large to be immediate. One below half a word is held in
  the word itself and counts nothing.

Everything else counts nothing: words, numbers known to fit a width, a
type whose constructors have no fields, held as its tag, and a
one-constructor wrapper, which is held as what it wraps. Data known before
the program runs, such as a string literal, is laid out in the image with
a count that marks it static, and is never written or freed.

## Where counts are placed

Lowering places every retain and release, after the program's
representation is chosen:

- A value's claim is released right after its last use, not at the end of
  a scope.
- A use that keeps a value, such as a field of a new cell, a loop's state
  or an owned parameter, takes the value's own claim where that use is its
  last, so nothing is retained only to be released.
- A parameter nothing in its function keeps is borrowed: its caller still
  holds it, and passing it costs nothing.

When the last claim on an object goes, its fields are released and its
block returns to a private heap. Where the heap is full, it asks the target
for more; where there is no more, the program exits with status 2.

## Writing in place

A buffer whose count is one is held by nothing else, so the sequence may be
written where it lies:

- **Adding to the front** writes into room before the sequence, where there
  is room.
- **Replacing an element** writes over it.
- **Otherwise** the sequence is copied first, to a new buffer with as much
  room again, which makes a run of additions cost a bounded number of
  copies each. This is copy-on-write.

Where it is known before the program runs that a buffer is held by nothing
else, as for one a loop rewrites every round, the count is not asked at
all; this is done for buffers whose elements hold no counts. Above that,
Barb rewrites a walk that builds a list the same length as the one it
walks, as `map` does, into one that replaces each element where it lies.
So in n-body, five bodies stepped five million times, a step builds no list
at all.

Cells are not written in place. A cell whose fields are its only readers
is not built at all: each field is read where it was made.

## Rationale

### Why reference counting and not a tracing collector?

A count of one says that nothing else can see a value, and that is what
lets an immutable list be written in place. A tracing collector knows
nothing about a value between collections, so a language built on one
copies or adds mutation to the language. In n-body, writing lists in place,
with the fusions it allowed and knowing statically which buffers are
unshared, took a step from 866 cycles to 309; see
[n-body](../nbody-performance.md).

Counting also needs no collector: no pauses, no finding roots in every
frame, and memory given back right after its last use. The same few
routines, written in machine IR, serve x86-64, wasm32 and a 6502 with a
16-bit address space.

The cost is the counting itself. A baseline profile of n-body spent 8% of its
time releasing cells and buffers, and 36% allocating, for lists a C program
keeps in one array. The recourses are the ones above: borrowed parameters,
claims moved rather than copied, and uniqueness known before the program
runs.

### Why can no value hold itself?

A cycle needs a value that points back at one built after it, and Faun has
no way to make one. Values are immutable, so nothing is changed to point
elsewhere once built. Evaluation is strict, so every field exists before
the value holding it. There are no references, and functions are not
values, so no closure can hold the value it lives in. A value defined in
terms of itself is never finished, rather than built as a loop.

So reference counting frees everything a program drops, with no cycle
collector beside it. The cost is that a structure with a back edge, a
doubly linked list or a graph whose nodes point at each other, is held as
data that names its parts: a node's neighbours as indices or keys in a
`Map`, as the graph library holds them.

### Why no borrow or lifetime syntax?

A value cannot change, so any number of holders may share it, and a count
decides when it is freed. Nothing a borrow would protect against can
happen: there is no write through one name that another sees. Whether a
parameter is borrowed or owned is a fact the compiler infers, for speed
alone.

The cost is that how a program performs rests on facts it does not write:
whether a buffer is shared, whether a parameter is borrowed. A program
cannot ask to be told when an update it expected in place copies.
`faun emit target` prints the program with every count placed.

### Why is writing in place invisible to a program?

Values have no identity. There is no pointer equality, no address and no
reference in the language, and Barb forbids them below it. A buffer is
written in place only where nothing else holds it, so no other name can
see it change; anywhere else it is copied first. Either way, every name
holds the value it was bound to: `snapshot = order` stays what it was when
`order` is bound again.

The cost is that the difference shows only in time. Keeping an old value
alive, as `snapshot` does, makes the next update of `order` a copy of the
whole list. The recourse is to let a name die before its value is
updated, which a loop that binds a name again does.

## Related

- [Architecture](architecture.md): the tiers, and where the machine tier
  stands among them
- [Effects](../forms/effects.md): files, which are closed explicitly where
  memory is freed implicitly
- [Collections](../values/collections.md): `List`, `Str` and `Map`, the
  values held in buffers
- [Pattern matching](../forms/pattern-matching.md): binding a name again,
  which lets the old value die
- [N-body](../nbody-performance.md): measurements of writing in place
- [Machine IR, archived](../archive/machine-ir.md): cells and buffers in
  detail, partly out of date
