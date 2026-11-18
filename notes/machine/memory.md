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
a count that marks it static, and is never written or freed. So is a
cell with no fields, a constructor such as `Continue` of a sum whose other
constructors have them: every one is the same, so each constructor's is
one static cell, and making one allocates nothing.

A constant worked out as the program runs, such as a table too large to
fold, is not static: the entry builds it and hands it down as a parameter
([computation](../computation.md#a-constant-is-worked-out-once)), so it is
counted like any value, borrowed by each definition passing it on, copied
before a write while shared, and freed once nothing still running can read
it.

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
for more; where there is no more, the program exits with status 2. Where a
call goes deeper than the stack has room for, an x86-64 Linux or 6502
program says `stack overflow` on standard error and exits with status 3.
A 6502 program without recursion whose calls could go that deep is refused
when it is built.

## Writing in place

A buffer whose count is one is held by nothing else, so the sequence may be
written where it lies:

- **Adding to the front** writes into room before the sequence, where there
  is room.
- **Joining two sequences,** `a.concat(b)`, writes `b` into room after `a`
  where nothing else holds `a`'s buffer and it has the room. Otherwise, on
  x86-64 and wasm32, `a` is written into room before `b`, where nothing
  else holds `b`'s buffer and it has room before or is strictly longer, so a
  sequence built by joining pieces before it, `[x].concat(built)`, grows at
  its front as one built by joining pieces after it grows at its end. That
  choice is a routine for each element layout a program joins, which every
  join calls: a program joining often is smaller for it, and a tiny one
  joining once larger, which `faun build --small` leaves out where it is.
  The 6502 joins only after the first: its calls carry four values and
  answer one, and the routine takes six and answers two.
- **Joining a sequence to a run of itself,**
  `out.concat(out.drop(k).take(n))` as an LZ77 copy writes it, writes the
  run after `out` where it lies. The run is a view of `out`'s buffer, so the
  buffer has two claims at the join, `out`'s and the run's; the join gives
  up the run's first, which never frees the buffer while `out` holds it,
  and then finds it held once. The run lies before where the writing
  starts, so it is read whole before anything is written over; where the
  buffer has no room and is copied, the run is read from the copy. This is
  done where both sides of the join are the same buffer in the program,
  as they are when the run is taken where it is joined.
- **Replacing an element** writes over it.
- **Otherwise** the sequence is copied first, to a new buffer with as much
  room again, which makes a run of additions cost a bounded number of
  copies each. This is copy-on-write.

A buffer is held once at a write only if nothing read after the write
holds it too. So a pure read of a sequence, and the runs of it the read
takes, written after a write of the same sequence is worked out before the
write wherever everything it reads is known there: in
`{head: head.put(key, at), prev: prev.put(at, head.get(key).ok_or(0))}`,
the `get` of `head` goes before its `put`, and the `put` writes in place.
Barb's cleanup does this; reads are pure, so the order they run in is not
observable.

Where it is known before the program runs that a buffer is held by nothing
else, as for one a loop rewrites every round, the count is not asked at
all; this is done for buffers whose elements hold no counts. Above that,
Barb rewrites a walk that builds a list the same length as the one it
walks, as `map` does, into one that replaces each element where it lies.
So in n-body, five bodies stepped five million times, a step builds no list
at all.

Cells are not written in place yet: building a cell as one of the same
size dies, as a tree's insert does, frees one and allocates the other.
Writing the new cell into the old one, touching only the fields that
change, is planned. A cell whose fields are its only readers is not built
at all: each field is read where it was made.

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

### Why does the compiler move reads before writes rather than the program?

The order a program reads and writes a list is fixed by how it is
written: a record's fields left to right, an argument before its call.
Whether a write is in place depends on that order, and nothing in the
source says so. Hash chains' insert reads the old head in its second field
after its first field writes the new one, and copied all 1024 heads every
byte; a run of `out` joined to `out` held its buffer twice and copied the
whole window every match, quadratic in the output. Both are written the way
the algorithm reads, and a programmer who does not know the rule above has
no way to find it but a profile.

Moving a pure computation earlier is semantics-preserving: it reads only
values, and Barb already moves pure work to either side of an effect and
leaves out what nothing needs. So the compiler, which knows where a write
is and what reads the written value afterwards, puts the reads first. The
cost is a rule with an edge: only a read whose inputs are all known before
the write moves, only after a write Barb recognizes as replacing, adding
or joining, and a run joined to its list is written in place only where the
run is taken in the same function as the join. The recourse elsewhere is
still to bind the read first.

### Why not a standard-library `extend_from`?

Rust's `extend_from_within` appends a run of a vector to itself in place.
The same in Faun, `List.extend_from(out, from, count)`, was proposed by the
[compression](../compression.md) note. Once a run of a list joined to it is
written in place, `out.concat(out.drop(from).take(count))` is that, written
with the words a reader already knows, and every program joining a list to
a part of itself gets it without learning a new name. An LZ77 copy whose
distance is shorter than its length repeats what it writes, which neither
`concat` nor `extend_from_within` does, so a decoder still copies that case a
byte at a time.

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

## History

- **2026-11-17:** a run of a list joined to the list is written in place,
  and a pure read of a sequence is worked out before an earlier write of
  it. Before, a view held across a join made inflate's slice copy
  quadratic, 8.2 billion instructions for 300 KB, and a record whose
  second field read what its first wrote over copied the whole list.
  Inflate's slice copy now takes 49 million for the 300 KB, and the flate
  library copies a match that does not overlap as a run of the window.

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
