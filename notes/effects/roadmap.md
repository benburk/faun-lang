# Roadmap: from today's host modules to the mature shape

**Status: proposal.** How the current host modules
(`crates/faun/standard/hosts/*.fn`) compare with the other notes, the small
fixes worth making now, and the order to add effects in.

## Where we are

The foundation is sound. The hardest pieces already exist:

- **Authority as a value.** `Host` has a private constructor, startup fields
  are produced only if read, and each target mounts its own host module at
  `std.host`.
- **Weak primitives in the host, loops in Faun.** Four descriptor routines
  plus `exit!`. `write_all!`, `read_to_end!` and the runners are Faun
  code.
- **Linearity.** `crates/faun/src/linearity.rs` infers borrow and consume,
  and refuses drops, double use, and `?` while a resource is held.
- **Bytes handed over without copying.** `Takes::Bytes` and
  `Returns::Filled`.
- **Confinement.** Linux opens with `openat2` and `RESOLVE_BENEATH`, and WASI
  uses its preopens.

The gaps are breadth (no clocks, entropy, environment, sockets or processes),
a routine vocabulary that answers only one word or one filled buffer, the
routine catalog living in `faun_core`, and no poller or reactor.

## Small fixes to the existing host modules

**Status: done.** All eight are in the host modules now. What each became:

- `exit!` takes a `U8`, so a status worked out from a `Nat` says
  `U8.of_nat(n)`. The success-or-failure split is not made.
- `read!` answers `Chunk = [Data(List(U8)), End]`, and a read asked for none
  answers none without asking the target.
- `close!` answers `Result({}, CloseError)`.
- The rows are `OpenError`, `ReadError`, `WriteError` and `CloseError`, all
  structural aliases, with `IoError` their union for a program's own
  signatures. `IoError.*` is no longer an import; tags need none.
- The Linux target ignores `SIGPIPE` before anything else runs in a program
  that writes, so every write reports `BrokenPipe` as a value, on every
  target: 25 bytes of code, hello world included. Go's split was considered
  and set aside; see "Broken pipes" in [console.md](console.md).
- Linux opens every file with `O_CLOEXEC`.
- `Fd : [Fd(U32)]`, and `[Fd(U16)]` on sim65, which has 16-bit words.
- `hosts/common.fn` holds the rows, `Mode`, `Chunk` and every loop, imported
  as `hosts.common`. The loader already allowed it: a host module resolves
  imports from the standard package's root.

Costs: statuses computed from a `Nat` now pay a real modulo where the machine
tier can't see the guard that bounds them (up to 44 bytes on WASI in the test
corpus), and the recorded sizes say why. Narrowing a value refined by its
branch would win it back, as `expression_cost.rs` already notes.

What each fix was, as proposed:

1. **`exit!` silently wraps.** Linux keeps only the low 8 bits of the status,
   so `host.exit!(256)` reports success. `examples/main.fn` exits with the
   argument count, which is the case where this bites. Take a `U8`, or split
   into `exit! : (Host, [Success, Failure]) -> []` and `exit_code!` (see
   [console.md](console.md)).
2. **Answer `End` instead of an empty list.** `read!` answers `[]` at end of
   input, which can't be told apart from a zero-byte request. Use
   `[Data(List(U8)), End]`. `read_chunks!` and `read_on!` get simpler.
3. **Drop meaningless numbers from results.** `close!` answers
   `Result(Nat, IoError)` where the `Nat` is always 0. Answer `{}`.
4. **Narrow the error rows.** A stream `read!` or `write!` can't meet
   `NotFound`, `IsADirectory` or `NotEmpty`. Give streams
   `[BrokenPipe, NoSpace, Denied, Other(Nat)]` and keep the wider row for
   `open!`. Faun's tag rows join where `?` meets them, so callers lose nothing.
5. **`BrokenPipe` can't happen on Linux today.** No `SIGPIPE` disposition is
   set, so writing to a closed pipe kills the process before the tag is ever
   answered. Either ignore `SIGPIPE` at startup, so the write answers
   `Err(BrokenPipe)`, or remove the tag from the Linux row. Ignoring is the
   more consistent choice.
6. **Open with `O_CLOEXEC`.** Linux's `flags(Mode)` doesn't set it (it is
   `0x80000`). Nothing notices until processes exist, and then every open file
   leaks into every child. It's free to add now.
7. **Wrap descriptors in a fixed-width `Fd`.** `File : [File(Fd)]` with
   `Fd : [Fd(U32)]`, and `U8` on sim65 (see "Representing resources" in the
   [README](README.md)).
8. **Share the portable half.** The three host modules are about 335 lines
   each, and differ only in the open flags, the error-number table, the word
   size, and nul-termination. `read_chunks!`, `write_rest!`, `read_text!`,
   the runners and the reporting are already generic over `where` bounds and
   could live in one shared module. The loader resolves imports relative to
   the importing package, so a shared `hosts/streams.fn` looks possible. I
   haven't tried it.

## Effects to add next

The ordering principle: first the effects that fit the routine shapes we
already have, then the ones that need new shapes.

A useful discovery: **filling a buffer and parsing it in Faun covers
structured results.** Linux's `statx` and `getdents64`, and WASI's
`path_filestat_get` and `fd_readdir`, all write a struct or a run of records
into caller memory. That is `Returns::Filled`, the shape `fd_read!` already
uses. Each target's host module parses its own layout. That's fine, since
host modules are per target anyway.

### 1. Entropy

- **Shape:** fill a buffer, exactly like `fd_read!`.
- **Linux:** `getrandom(buf, len, 0)`. **WASI:** `random_get(buf, len)`.
  **sim65:** omit.
- **Why first:** it's the smallest possible new routine, and it unlocks
  seeded hashing that can't be predicted, randomized tests, and UUIDs.

### 2. Clocks and sleep

- **Shape:** a 64-bit value. Linux's `clock_gettime` fills a 16-byte
  `timespec`, and WASI's `clock_time_get` writes a `u64` through a pointer, so
  both are "fill a buffer". Sleep is `clock_nanosleep` on Linux, and
  `poll_oneoff` with a clock subscription on WASI.
- **Why:** programs can time themselves. The MD5 benchmark could report its
  own hashrate instead of relying on `perf`. Timeouts need it, and so does the
  reactor's `After` source.
- **API:** `Monotonic.now!`, `Monotonic.sleep!`, `WallClock.now!`, as sketched
  in the [README](README.md). sim65 omits them.

### 3. Environment

- **Shape:** a startup value, like `args`. On Linux the environment follows
  `argv` on the startup stack. WASI has `environ_sizes_get` and `environ_get`,
  which mirror its argument calls.
- **API:** `host.env`, with a pure `get` (see [console.md](console.md)).
  Produced only if read, like `args`.

### 4. File namespace operations

- **Shapes:** "name plus scalars, answering a status" (the `fd_open!` shape)
  for `make_dir!`, `remove!` and `rename!`; "fill a buffer" for `stat!` and
  `list!`.
- **Linux:** `mkdirat`, `unlinkat`, `renameat2`, `statx`, `getdents64`, all
  relative to the root descriptor. **WASI:** `path_create_directory`,
  `path_unlink_file`, `path_remove_directory`, `path_rename`,
  `path_filestat_get`, `fd_readdir`.
- Add positional `read_at!`/`write_at!` (`pread64`/`pwrite64`, `fd_pread`/
  `fd_pwrite`), and split `File` into `Reader`, `Writer` and `File` (see
  [files.md](files.md)).
- **Why:** with these, real tools become possible: a `find`, a `du`, a static
  site generator, and the atomic `write_file!` helper.

### 5. Blocking TCP (Linux first)

- **Shapes:** `socket`, `connect`, `bind`, `listen` and `accept4` all take
  scalars plus a `sockaddr`. Faun builds the `sockaddr` as bytes, handed with
  `Takes::Bytes`. Reads and writes reuse the stream routines on the socket's
  descriptor.
- **Targets:** Linux only at first. WASI preview 1 can't create sockets, and
  sim65 has none.
- **Why:** it's the first effect that makes Faun useful for services. A
  blocking server that handles one connection at a time is enough to exercise
  the API and the linearity rules before the poller exists.
- `accept4` also answers the peer's address, which is the first case that
  wants two results. Filling a buffer with the `sockaddr` covers it.

### 6. Processes (Linux first)

- **Needs new target work:** the child side of `clone3` runs between the
  clone and `execve`, and the target has to emit it directly.
- **Shape:** `Child` is a pidfd, which makes `wait!` and `kill!` ordinary
  descriptor calls and lets the poller wait on it later (see
  [processes.md](processes.md)).
- Do the `run!` form (collect stdout and stderr) first. It needs `poll`
  inside the host routine, which is a small, contained first use of it.

### 7. The poller

- `epoll_create1`, `epoll_ctl` and `epoll_wait` on Linux. On WASI preview 1,
  `poll_oneoff` covers the clock and stream sources it has.
- Batch `main!` use first (see [events.md](events.md)), then the reactor
  entry profile once the memory story for state that survives activations is
  settled.

### Later

Audio, windows and graphics, and anything behind a C library, wait for the
structural steps below.

## Structural steps, in order

1. **Move the routine catalog into the target crates.** Core keeps the
   vocabulary (`Takes`, `Returns`, `consumes`); each target registers its own
   routines. This should happen before the list grows much.
2. **Share the host module's portable half** (fix 8 above), so that adding an
   effect means writing its target-specific part only.
3. **Extend `Returns` with several scalar results.** Filling a buffer covers
   most cases; this covers the rest cleanly, and the C binding layer needs the
   same thing for out-parameters (see [bindings.md](bindings.md)).
4. **A conformance test per contract.** The same Faun program runs on every
   target that claims a contract, and the outputs must agree. Much of the
   suite already runs programs across the three backends, so this is mostly
   organization.
5. **Calling C symbols, then dynamic linking**, when the first macOS target
   or the first library binding needs them.
