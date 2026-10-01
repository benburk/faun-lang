# Host effects: brainstorm

**Status: brainstorm.** Nothing here is implemented beyond what
[host-effects.md](../host-effects.md) and `crates/faun/standard/hosts/*.fn`
already describe. The notes sketch which host modules Faun should have, what
their APIs could look like, and how to choose semantics that stay portable and
still compile to the platform's cheapest primitive.

The starting point is Ori's effects design
(`../ori-lang/notes/design/effects.md`,
`reactor.md`, `linearity.md`), which Faun inherits: authority enters through
`main!(host)`, effectful names end in `!`, host resources are linear and closed
explicitly, and a long-running program is driven by a host-owned reactor rather
than by async or threads.

## Notes

- [wasi.md](wasi.md): where WASI came from, and what to take from it and what
  to leave
- [console.md](console.md): args, environment, stdin, stdout, stderr, exit,
  terminals
- [files.md](files.md): rooted directories, files, and whole-file helpers
- [processes.md](processes.md): spawning, pipes, waiting
- [network.md](network.md): name resolution, TCP, UDP
- [events.md](events.md): the reactor, with completion-shaped custody
- [audio.md](audio.md): audio output and input
- [graphics.md](graphics.md): windows, input, pixels, GPUs, and
  target-specific graphics
- [bindings.md](bindings.md): calling C libraries without exposing C, and the
  adapters that turn callback APIs into events
- [roadmap.md](roadmap.md): how the current host modules compare, small fixes
  to make now, and which effects to add next

## What the host API is for

A host API answers four questions for a program:

1. **What may it touch?** Authority. A value the program was handed, never
   a global it can name.
2. **What does the call mean?** Semantics the program can rely on on every
   target that claims the contract.
3. **What does it cost?** Ideally one platform primitive per call, with no
   runtime layer hidden between them.
4. **Where can it run?** The contracts a program requires, checked at compile
   time against what a target provides.

Everything below is a consequence of taking all four seriously at once.

## Goals

- **No ambient authority.** `Host` is the root. Components such as `Stdout`,
  `Dir` or `Network` are derived from it by pure selectors and can be handed to
  a library on their own. Importing a module grants nothing.
- **Portability means checked requirements, not lowest common denominator.**
  A target implements only the contracts it can honor exactly and omits the
  rest. A program using only `Stdout` runs on sim65. A program using `Gpio`
  runs only on boards. Neither is a failure.
- **Weak primitives in the host, strong guarantees in Faun.** The host exposes
  the weakest guarantee that every good platform primitive already gives, such
  as a partial write. Stronger guarantees, such as writing everything or
  replacing a file atomically, are Faun library code over those primitives.
  This keeps the trusted surface small and the per-call cost at one primitive.
- **Bytes cross where they lie.** A write hands the list's own storage to the
  target, and a read fills storage the target is handed. No copying at the
  boundary, and no allocation inside the host.
- **Every host call returns.** A call may block, but no call takes over the
  program's control flow. A program that lives forever is a reactor (see
  [events.md](events.md)), with the loop below Faun.
- **Resources are linear, and no cleanup is implicit.** Files, sockets,
  children, windows and audio streams are closed by an explicit `!` call on
  every path. The compiler never chooses between close and flush, or between
  wait and kill.
- **Errors are small closed tag rows per operation.** Faun's structural tags
  let `connect!` answer `[Refused, Unreachable, TimedOut, Denied, Other(Nat)]`
  without one umbrella `IoError` type. A caller's `?` joins the rows it meets.
  `Other(Nat)` keeps the platform code for logging, never for portable logic.
- **Programs can be tested without a real host.** Capabilities are used
  structurally, so a test can hand a helper a scripted fake that has the same
  methods. The interpreter can run a whole program against a scripted host.

## How to pick a portable semantics

For each proposed operation:

1. **List the cheapest primitive on each target family.** At minimum these are
   Linux syscalls (the x86-64 target is a static ELF with no libc), WASI
   preview 1 today and 0.3 later, macOS and Windows through their system
   libraries, the browser through JavaScript imports, and a small board or
   sim65.
2. **Take the intersection of their guarantees.** That is the contract. A
   guarantee that one family cannot give without an emulation layer does not go
   in the contract.
3. **Require O(1) primitives per portable call.** If a target needs a loop, a
   helper thread or a shadow data structure to meet the contract, then either
   the contract is wrong, or that target should omit it and offer its own.
4. **Put the loop in Faun, not in the host.** `write_all!` and `read_to_end!`
   already work this way. That code is checked and portable, and the
   target writes it only once.
5. **Split a capability wherever a launcher would reasonably grant only part
   of it.** Examples: reading files versus writing them, connecting versus
   listening, and `exit!` with any code versus plain success or failure.
6. **Name the non-portable part.** Case sensitivity, timestamp precision,
   directory order and durability are host properties. Document them, and
   don't pretend they are uniform.

A useful check: the contract should read as though it were written for the
most restrictive serious target (WASI or a board), while the Linux mapping
stays one syscall.

## Module map

The capability tree, as selectors on `Host`. Each line is an optional contract.

```text
Host
  args, raw_args            startup values (fields; unread ones are never produced)
  exit!                     Success/Failure; exit_code! is a separate contract
  stdin, stdout, stderr     byte streams
  terminal                  size, raw mode, is_terminal
  env                       allowlisted environment snapshot
  clock                     wall time
  monotonic                 instants, sleep!
  entropy                   secure random bytes
  dir / read_dir            rooted directory capabilities (read-write / read-only)
  processes                 spawn!, run!
  network                   resolve!, connect!, listen!, bind_udp!
  audio                     open_output!, open_input!
  display                   open_window!, and then surface or gpu per window
  <target-specific>         gpio, ppu, metal, vulkan, win32, ...
```

Clocks and entropy are small enough not to need their own notes:

- `WallClock.now! : WallClock -> Time`: nanoseconds since the Unix epoch as
  an `Int`. It may move backwards.
- `Monotonic.now! : Monotonic -> Instant` never decreases within one
  invocation and is comparable only within it. `Monotonic.sleep! :
  (Monotonic, Duration) -> {}`.
- `Entropy.fill! : (Entropy, Nat) -> List(U8)` returns cryptographically
  secure bytes. Seeded pseudo-random generation is pure library code and needs
  no capability.

## Representing resources

A resource type is concrete inside its target's host module and opaque
everywhere else. That is what Faun does: `File : [File(Fd)]` with the
constructor unexported, so only the host module can build a `File` or take one
apart. Lowering treats a one-constructor wrapper as transparent, so a `File`
costs one register.

Keeping the payload visible to the host module is deliberate. The host module
is trusted Faun code, and it needs the handle to share routines: `Stdout` and
`File` both write through one `fd_put!`. A fully opaque, target-represented
type would turn every method into its own routine and add a compiler concept
that private constructors already cover. Portability is unaffected, since
portable contracts are method signatures and constraint aliases, which never
mention the payload.

The backing type differs per target, and is fixed-width rather than `Nat`:

- **Fixed width.** `U32` for Linux and WASI descriptors, `U16` on sim65,
  whose word is 16 bits, and `U64` for a future Windows `HANDLE`. `Nat` is
  unbounded, so a descriptor's width would rest on range analysis.
- **One private handle type per target**, wrapped by each resource:

  ```faun
  Fd : [Fd(U32)]               # private to the host module
  File : [File(Fd)]
  Dir : [Dir(Fd)]
  TcpStream : [TcpStream(Fd)]
  ```

  Routines take an `Fd`, so even inside the host module a byte count can't be
  passed as a descriptor. Linearity follows the nominal type, not the payload:
  `File` is linear because something consumes it, while a root `Dir` holding
  the same `Fd` stays unrestricted because nothing does.

- **Records for compound backing.** A Wayland window is several protocol
  object ids plus a shared-memory descriptor:
  `Window : [Window({surface: U32, pool: Fd})]`. Containment makes the whole
  record linear.
- **No derived `equals`, `to_str` or `hash_into` on resources.** Descriptor
  numbers never reach output, and resources can't be compared, which the
  reactor's custody design relies on.

## Target families

What the lowest stable interface to the operating system is decides how a
contract is implemented:

- **Linux:** syscalls. Static ELF today; libraries (Vulkan, ALSA) need
  `dlopen` and so a dynamic variant.
- **macOS:** `libSystem`. Raw syscalls for `write` and `exit` work in
  practice, but Apple doesn't promise them and has changed others:
  `gettimeofday`'s return convention changed in 10.12 and broke Go binaries,
  and Go has gone through `libSystem` since 1.11. Every macOS process loads
  `libSystem` from the shared cache anyway, so always linking it costs one
  indirect call per operation and keeps the binary a single file.
- **Windows:** `kernel32`/`ntdll` and other DLLs. UTF-16 names;
  completion-based I/O.
- **WASI:** imports (`wasi_snapshot_preview1` today). Preopens as roots; 0.3
  moves to components and async.
- **browser:** JavaScript imports. No blocking on the main thread, so only the
  reactor fits.
- **sim65 / boards:** ROM routines, MMIO, simulator hooks. Tiny memory; most
  contracts are simply absent.

Linux is unusual: its syscall ABI is stable, so a Faun binary needs nothing
else. That makes it possible to speak Wayland over a raw socket, or to drive
`/dev/snd` and DRM with ioctls, but not to use Vulkan, which lives behind a
loader library.

## Open questions

- How does a host module declare that one contract is split from another
  (`ReadDir` versus `Dir`) without duplicating every method?
- Should portable contracts be versioned packages (`std.host.files.v1`), or
  constraint aliases that the target modules satisfy?
- Does the requirement report ("this program needs `Stdout` and `ReadDir`")
  become a manifest a launcher enforces, as WASI worlds are?
- Reactor entry spelling: reserved `init!`/`handle!`/`finish!`, as Ori leans,
  or something in the host module.
