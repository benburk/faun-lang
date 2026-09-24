# Host interface

How a program reaches something outside it, and how a target says what it
can reach. Draft.

## Goals

- A target says what it answers for once, in one place, and every tier reads
  that rather than assuming.
- Value semantics survive contact with C. No pointers in the language, no
  aliasing, no mutation of a value.
- Resources such as files and device contexts, tracked linearly by the
  frontend so one cannot be used after release.
- Nothing is silently truncated at the boundary.
- barb and ir learn nothing about either end.

## Not doing

Each of these was tried in the design and dropped for the reason given.

- **A general declaration format.** A `.host` file with signatures,
  providers and ownership annotations is a C header, and a C header works
  only because a C compiler stands behind it supplying layout, aliasing
  rules and lifetimes. A format expressing all of that would be a research
  language. One expressing less would be C's unsafety with new syntax.
  Targets bless libraries in Rust instead.
- **Binding a library without recompiling.** This was the goal the format
  served. It was serving a user who does not exist, and buying a format that
  could not express what that user would need.
- **Frontends sharing one host vocabulary.** faun is a demo and the language
  that replaces it is a second frontend in sequence, not a second frontend
  at once. Sequential frontends need barb not to rot, which is already true,
  rather than a stable interface between them. The cost of the requirement
  was a `Kind` indirection, a materialising step for declared types, and no
  way to use records.
- **Pinned struct layouts.** A binding reads a record's fields and writes
  them into a region it lays out in C terms, so the program's record keeps
  whatever representation `ir` chose. Costs a copy per call, which is free
  for a struct built at startup and real for one built per frame.
- **Pointers and buffers in the language.** A binding allocates, calls,
  copies out and frees. Nothing user-visible holds an address, so there is
  nothing to leak and nothing to use after free.
- **Inline assembly in a declaration.** A file says where something is; the
  target's code says what it does. Writing instructions is saying what it
  does.
- **Signed fixed-width numbers.** The language has no negative number
  anywhere. An `I32` at the boundary would be the only place one existed,
  and nothing could be done with it. Widths are unsigned, and `-1` arrives
  as a bit pattern.
- **Static libraries.** A symbol resolved at link time is a different
  mechanism with a different cost, and nothing wants one yet.
- **More than one abi per target.** No 32-bit Windows. A target with two
  conventions is two targets, and then neither has a choice to express.
- **Effectful callbacks.** The effect model is that order is dataflow, and a
  callback's invocation has no dataflow edge from the program. Nothing
  upstream of it holds a world value to thread in.

## Shape

### Where the coupling is

barb and ir are the waist and see only representations and constraints. A
width is a constraint. A resource is a type with no constructors at a
declared class. Neither mentions a frontend or a machine.

The frontend and the target couple above and below that waist, which is what
clang does for FFI while LLVM IR stays the waist. A target's bindings may
know the frontend's standard library, because bindings are per-target code
that a new frontend rewrites anyway.

The rule that replaces the dropped requirement: if something cannot be said
as a representation or a constraint, it belongs above the waist or below it.
Once a target crate can see the frontend, the shortest path to any problem
runs through putting a frontend concept in `ir`, and nothing structural
stops that.

### What a blessed library is

A target ships bindings for the libraries that matter and cannot be written
in the language: its syscalls, and things like Metal or CUDA. Each declares
routines and knows how to lower a call to one.

Lowering splits the way everything else does. Marshalling happens in
`ir::lower`, which has types and picks representations. Emitting the call
happens in the target, which has registers and instructions.

Anyone needing a library nobody blessed writes a crate depending on the
target and registers more routines. That is the extension point, and it
costs about one trait.

### Portability by name agreement

Targets coordinate on spelling the common effects, and a program using that
subset compiles anywhere without changes. Nothing enforces the coordination,
so a test over the names more than one target declares is what catches
drift, and it doubles as the only document of the portable surface.

Units and meaning stay on human attention. Two targets declaring
`clock!(…) -> Nat` where one answers milliseconds and the other ticks passes
every structural check.

### Resources

A resource is a type a binding declares and no program can write. It has no
constructors, so nothing can forge one, and a width from the declaration
that bounds never narrow. Ordinary code being unable to declare one is what
lets an api take a `File` where it would otherwise take a number somebody
could have made up.

Linearity over a resource belongs to the frontend. It buys lifetime safety,
meaning no use after release and no leak, rather than in-place mutation.
In-place is free already, since a resource was never a value. Duplicating a
handle is harmless, because every access is a threaded effect call and there
is no unordered access to create. Consumption is what needs tracking.

### Structs

Two ways, and the first covers what is reachable today.

The binding owns the struct. The program passes scalars and handles, and the
binding fills in the fields it knows. That often reads better than the C it
wraps: `connect!(sock ip port)` beats building a `sockaddr_in` with a family
tag and a byte-swapped port.

For an api where that stops scaling, such as Vulkan, a frontend module
declares the record in ordinary source and programs build it with ordinary
constructors. The binding states the shape it needs, the check runs when the
program is read, and a mismatch names the module.

barb records carry no field names, so that check is positional. Field types
catch most reorderings and catch none between adjacent fields of the same
type. Generate the module and the binding from one description rather than
writing two hundred struct definitions twice.

### Callbacks

A pure callback is reachable once barb can name a function as a value, which
is one new expression form and the first thing that is not first-order. It
changes reachability, since a function whose address is taken is live
whether or not anything calls it.

An effectful callback is not reachable, which rules out GUI toolkits, audio
render callbacks, and `pthread_create`. Systems, networking, storage and the
core paths of OpenGL, Vulkan, Metal and CUDA are all callback-free.

## Interfaces

Backend to frontend, saying what a program may name:

```rust
pub struct Routine {
    pub name: String,
    pub takes: Vec<Class>,
    pub answers: Option<Class>,
    pub comes_back: bool,
}
```

Frontend to backend, saying which of its types stand for what:

```rust
pub struct Standard {
    pub number: barb::TypeId,
    pub bytes: barb::TypeId,
    pub named: HashMap<String, barb::TypeId>,
}
```

`parse` returns `Standard` rather than taking it, since those ids do not
exist until parsing has made the types. `called`, `authority` and
`hands_back` come off `Routine`, because each is the frontend's business and
the frontend now keeps it.

## What exists

- Primary applications define the exact, bodyful entry `main! : Host -> []`
  and import `Host` and `exit!` from the compiler-mounted `std.host` module.
- Each initial host declares private-constructor `Host : {argc: Nat}` and
  bodyless `exit! : Host Nat -> []`. Barb keeps `main!(host: Host)` as its
  entry, including the `Host` wrapper, startup record, and projections. Machine
  lowering represents the current one-field host transparently; each target
  constructs the named `host` entry value, while lowering removes the authority
  argument before calling the machine provider.
- `platform::Routines`, a set a program is read against, with `builtin()`
  and `push`. The set moves into the targets.
- `Target::provides`, the names a target answers for. `accepts` refuses the
  rest.
- `barb::Function::outside`, which routine answers for a declaration, so one
  routine serves a program at more than one type.
- `Shape::Spine` and `intern_bytes`, recognising a list of numbers
  structurally and laying it out contiguously, with `address_of` and
  `data_len`.

## Open

- **`met()` converts where it should refuse.** `ir/lower.rs` inserts a
  `Convert` when a value does not fit what a routine takes, which is the
  machine deciding where `Op::Convert`'s own doc says a program asks. Latent
  while every routine takes a word.
- **Only scalar input is represented.** The target constructs the represented
  `host` entry value from `argc`, and every machine obtains it differently:
  Linux leaves it on the startup stack, WASI reports it through a call, and the
  simulator has a hook. `read_byte!` consumes stdin one byte at a time,
  answering zero at EOF or the byte plus one. Argument strings, whole input
  buffers, and strings still need computed aggregates to have a representation.
- **Narrowing needs recognition.** A program proves a value fits by clamping
  or taking a modulus, and `facts` recognises `add` and nothing else.
- **faun needs a prelude.** `Standard.number` has to point at a type, and
  every example declares its own `Nat`.
- **Computed lists have no representation.** A binding answering a
  `List(U8)` has to build one.

## Order

1. `met()` refuses rather than converts. Changes nothing today, and gets
   awkward once the first narrow routine exists.
2. Routines move into the targets, and the conformance test over shared
   names lands with them.
3. Imports in surface, which is also what lets a prelude exist. The entry
   rule stays either way: a program leaves through an effect answering
   the empty structural variant type `[]`, which asks for nothing a machine cannot do.
4. `Standard`, and borrow checking over resources.
