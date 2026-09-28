# Where WASI came from

**Status: background.** Faun's `wasm32-wasi` target imports
`wasi_snapshot_preview1` (`fd_write`, `fd_read`, `path_open`, `fd_close`). This
note traces how that interface came about and what came after it, because
WASI has already worked through most of the questions these notes ask.

## Lineage

1. **POSIX (1988 onward).** A process inherits ambient authority: a global
   filesystem namespace, a current directory, environment variables, signals,
   and any socket it cares to open. Every later design reacts against this.
2. **Capsicum (2010, Cambridge and FreeBSD).** Capsicum adds a _capability
   mode_ to FreeBSD. Once a process enters it, global namespaces are gone, and
   the process can act only through file descriptors it already holds, each
   carrying a set of rights. Paths are resolved relative to a directory
   descriptor and may not escape it.
3. **CloudABI (2014–2016, Nuxi, led by Ed Schouten).** CloudABI is a
   POSIX-like ABI made only of the capability-mode subset: no `open` of an
   absolute path, only `openat` from a descriptor that was handed in. Programs
   received their descriptors at startup through a configuration. It never
   became widespread, and its authors later pointed users to WASI instead.
4. **Emscripten (2011 onward).** Early wasm, and asm.js before it, emulated
   POSIX with JavaScript glue. That worked in the browser, but the
   "system interface" was whatever Emscripten's JS happened to do.
5. **WASI announced (March 2019, Mozilla).** Dan Gohman and Lin Clark
   ("Standardizing WASI") proposed a system interface for wasm outside the
   browser. The design borrowed CloudABI's capability model directly:
   _preopened_ directories stand in for CloudABI's startup descriptors, and
   every path operation is relative to one. Interfaces were described in
   `witx`, and the first frozen snapshot was `wasi_snapshot_preview1`, which
   is still the most widely deployed.
6. **The Bytecode Alliance (November 2019).** Mozilla, Fastly, Intel and Red
   Hat formed the Alliance to host Wasmtime, the WASI proposals and, later,
   the component model.
7. **The component model and WASI 0.2 (January 2024).** Preview 1 was a C
   ABI: integers, pointers into linear memory, and a function per operation.
   The component model replaced it with _WIT_, an interface language with
   records, variants, lists, strings, and _resources_ passed as `own<T>` or
   `borrow<T>` handles. WASI 0.2 was reorganized into packages: `wasi:cli`,
   `wasi:io` (streams and `pollable`), `wasi:filesystem`, `wasi:sockets`,
   `wasi:clocks`, `wasi:random` and `wasi:http`. A _world_ names the set of
   imports and exports a component needs, such as `wasi:cli/command`.
8. **WASI 0.3 (June 11, 2026).** Async moved into the component model itself
   as `async func`, `stream<T>` and `future<T>`, and the whole `wasi:io`
   package was removed. Its `pollable` resources composed badly when
   components were chained. Sockets collapsed from seven interfaces to two,
   and `connect` became one async call instead of `start-connect` plus
   `finish-connect`. Directory listing became a `stream<directory-entry>`,
   and stdio became a stream plus a future that reports completion. Wasmtime 46
   enables 0.3 by default, and 0.3.x point releases follow every two months.
   1.0 is the next milestone, with no fixed date.

## What Faun should take

- **Capabilities as values, rooted directories as the filesystem.** This is
  the Capsicum, then CloudABI, then WASI line, and Faun's `Files` already
  follows it. The x86-64 target does the Linux half of the same thing.
- **Typed resources with owned versus borrowed handles.** WIT's
  `own<T>`/`borrow<T>` is Faun's consume/loan split, written at the interface
  instead of inferred. When a call crosses into a WASI component, Faun's
  inferred disposition must agree with the WIT signature, and the host
  descriptor is where that agreement gets checked.
- **Worlds as named requirement sets.** A WASI world is a constraint alias
  over the host: `Cli(h) = where ...`. Faun's requirement inference already
  computes the world a program needs. Publishing it is the missing
  "authority manifest".
- **Per-interface error enums.** `wasi:filesystem` has its own `error-code`,
  and `wasi:sockets` has its own. This matches per-operation tag rows.
- **Interfaces split by what a launcher grants.** Clocks, random, filesystem
  and sockets are separate imports, so a component that never imports sockets
  cannot use the network. Faun gets the same property from structural
  requirements.

## What Faun should leave

- **Rights bitmasks.** Preview 1 gave every descriptor a pair of 64-bit rights
  masks (base and inheriting). They were hard to use, runtimes largely ignored
  them, and 0.2 did not carry them forward. Faun should split authority by
  _type_ (`ReadDir` versus `Dir`), not by bits on a handle.
- **Descriptor numbers and seek state.** Preview 1 kept POSIX's integer
  descriptors and a per-descriptor cursor. Faun's resources are opaque, and
  positional reads (`read_at!`) avoid cursor state where random access is
  wanted.
- **Async as the base layer.** WASI 0.3 is async-first because its hosts are
  servers and browsers that must multiplex, and because component composition
  needs a shared scheduler. Faun keeps a blocking core, which serves batch
  programs and small targets, plus a host-driven reactor for multiplexing (see
  [events.md](events.md)). A 0.3 target can implement the reactor on
  `future`/`stream`: each custody entry becomes a pending future, and waiting
  on all of them is the reactor's wait.
- **Traps for host failures.** Faun's host calls answer `Result`. A contract
  violation is a compile error, and a host failure is a value.

## The Faun WASI target over time

- **Now:** preview 1, which is a C ABI, fits a first-order language, and runs
  on every runtime.
- **Next:** a component target (`wasm32-wasip3` or later) that emits a
  component and imports 0.3 interfaces. Faun lists map onto `list<u8>`,
  closed tag rows onto `variant`, and resources onto `own`/`borrow`. Strings
  are already UTF-8, which matches WIT's `string`.
- **Always:** the WASI target adapts Faun's portable contracts to WASI. It is
  not a second design. If a WASI interface can't meet a Faun contract (0.2 and
  0.3 have no process spawning, for example), the target omits that contract.

## Sources

- [WASI 0.3 release notes](https://wasi.dev/releases/wasi-p3)
- [WASI roadmap](https://wasi.dev/roadmap)
- Lin Clark, "Standardizing WASI: A system interface to run WebAssembly
  outside the web", Mozilla Hacks, March 2019
- Robert Watson et al., "Capsicum: practical capabilities for UNIX", USENIX
  Security 2010
