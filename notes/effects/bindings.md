# Bindings: C libraries without C in Faun

**Status: brainstorm.** Faun source never sees a C declaration, a pointer or
a calling convention, and that stays true. This note is about making it cheap
for a _trusted_ binding to wrap a C library, so that blessing an API doesn't
mean hand-writing every function.

## What stays ruled out

The archived host-interface draft rejected a general declaration format: a C
header only works because a C compiler stands behind it and supplies layout,
aliasing and lifetimes, and a format that says all of that would be a
research language. That still holds. The proposal here is the opposite kind
of format: one that says very little, and refuses whatever it can't say.

## Where routines live

`Routines::builtin()` in `faun_core` currently lists every routine for every
target, and each target repeats the names in `provides`. That list moves into
the target crates. A target, or a binding crate a target depends on, registers
its own routines, and core keeps only the vocabulary for describing them
(`Takes`, `Returns`, `consumes`). The archived draft planned the same move.

## A flat-C vocabulary

`Takes` and `Returns` are already a small binding language: a scalar, bytes
handed where they lie, a filled buffer, a consumed argument. A few more words
cover a large share of C libraries that look like syscalls. The C header gives
types and the calling convention mechanically. A small annotation file adds
what the types don't say:

```text
library sqlite3 dynamic "libsqlite3.so.0"

type Db    handle
type Stmt  handle

open_v2(filename: in str, db: out Db fresh, flags: in u32, vfs: null)
    -> status(ok = 0)
prepare_v2(db: borrow Db, sql: in bytes(len = nByte),
           stmt: out Stmt fresh, tail: null) -> status(ok = 0)
step(stmt: borrow Stmt) -> code
column_blob(stmt: borrow Stmt, i: in i32)
    -> bytes(len = column_bytes(stmt, i)) copy_now
bind_blob(stmt: borrow Stmt, i: in i32, data: in bytes(len = n),
          destructor: const SQLITE_TRANSIENT) -> status(ok = 0)
errmsg(db: borrow Db) -> str copy_now
finalize(stmt: consume Stmt) -> status(ok = 0)
close_v2(db: consume Db) -> status(ok = 0)
```

The roles:

- **Scalars:** `in i32`, `in u32`, and so on.
- **Byte input:** `in bytes(len = p)` pairs a pointer argument with a length
  argument, both from one Faun `List(U8)` handed where it lies. `in str`
  appends a nul byte.
- **Output buffers:** `out buffer(cap = p, filled = ...)` gives C room inside
  a new list and sets the list's length from the return value or another
  out-parameter.
- **Handles:** `out T fresh` gives C a slot to write a handle into and
  creates a linear resource. `borrow T` and `consume T` feed straight into the
  linearity checker.
- **Out-scalars:** `out u64` answers an extra value beside the return value.
  This is the same extension `Returns` needs for host functions that answer
  several values, such as `accept` or `wait`.
- **Fixed arguments:** `null` and `const X` pin arguments the program must not
  choose. Pinning `SQLITE_TRANSIENT` removes a retained pointer, because
  sqlite then copies the data.
- **Returned pointers:** `copy_now` copies the result before the next call.
  `owned str(free = sqlite3_free)` copies, then frees.
- **Status codes:** `status(ok = 0)` becomes a `Result` with the code in
  `Err`.

From one file the tool generates:

1. **A Faun module:** opaque types with private constructors, and bodyless
   methods.
2. **Marshalling code in Machine IR** for each function: building the nul
   terminator, reading out-slots, copying returned bytes, mapping status to
   `Result`.

The target then needs to know only one thing: how to call a C symbol with
scalar and address arguments in its C calling convention (System V on x86-64,
AAPCS64 on ARM, Win64). Passing structs by value is the hard part of System V,
so the first version refuses it.

### What it refuses

- callbacks;
- pointers C keeps after returning, unless a `const` pins them away;
- structs containing pointers, such as Vulkan's create-info chains (a
  possible second version with nested marshalling);
- varargs;
- APIs that must be called from one particular thread.

Anything refused gets a hand-written adapter (below).

### Trust

A wrong `len =` is memory corruption. The annotation file is trusted code,
reviewed like a host module, and only a target or a binding crate may supply
one. The layer makes blessing cheap; it doesn't make it unnecessary.

### Where annotations come from

Some API descriptions already carry what C headers lack, and could generate
the annotation file:

- Vulkan's `vk.xml`: `len=` attributes, optional parameters, synchronization
  rules, and which call destroys which handle.
- Wayland's protocol XML: object creation and destructor requests.
- Microsoft's Win32 metadata: SAL annotations, and which function releases a
  handle.
- WIT: `own` and `borrow`.
- Clang's bounds attributes such as `counted_by`, which Apple is pushing into
  its own headers.

Everything else gets a hand-written file.

## Linking

- **Dynamic first.** Importing symbols from a shared library needs only
  dynamic-linking metadata in the executable. Most static C libraries depend
  on libc, so linking a `.a` means linking libc too.
- **macOS and Windows need it regardless.** macOS has no supported syscall
  interface, and Windows goes through DLLs. So "call a C symbol with the C
  convention" has to exist for those targets anyway.
- **Linux keeps both.** The static, libc-free binary stays the default. A
  dynamic variant adds an interpreter entry, `DT_NEEDED`, and calls through the
  global offset table, which is engineering work, not research.

## Adapters for what doesn't fit

What the flat vocabulary refuses is handled by a small set of adapter
patterns. Each pattern is written once, not once per API:

1. **Flat call:** a syscall-like function. Covered by the vocabulary.
2. **Handle lifecycle:** create, borrow, consume. Covered by the vocabulary.
3. **Notifying callback:** "something happened". The adapter queues an event
   and wakes the poller. A Win32 window procedure is mostly this.
4. **Demanding callback:** "give me samples now". The adapter answers from a
   ring buffer the program filled in advance, or with a default, then wakes
   the poller. CoreAudio, AAudio's callback mode and the browser's
   `AudioWorklet` all use this (see [audio.md](audio.md)).
5. **Buffer kept during an operation:** io_uring, overlapped I/O. The buffer
   and resource go into custody (see [events.md](events.md)).
6. **Shared-memory region:** `mmap`, Wayland's `wl_shm`, a GPU upload buffer.
   Faun has no addresses, so the region is a handle with copy-in and copy-out
   operations, as WebGPU's `writeBuffer` does.

Blessing an API means choosing a pattern per function and writing its Faun
types.

### Adapters in Machine IR

Patterns 3 and 4 run on a foreign thread and can't use Faun's runtime. Rather
than hand-written assembly per target, they could be written once in Machine
IR, which already has words and addresses. That needs two additions I don't
believe exist yet:

- atomic loads, stores and fences;
- an entry point callable with the C convention from a foreign thread.

With those, the ring-and-wake adapter is one piece of trusted Machine IR
shared by every backend. Only the wake call itself (`eventfd`, `SetEvent`,
`Atomics.notify`) stays per operating system.

## Protocols need no C

Wayland, X11, PulseAudio and D-Bus are byte protocols over a Unix socket.
With descriptor passing (`SCM_RIGHTS`), `memfd` and the shared-memory region
above, a window or an audio stream on Linux is Faun library code over sockets.
For those, the best binding is no binding.
