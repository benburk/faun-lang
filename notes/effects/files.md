# Files

**Status: brainstorm.** Today there is `Files.open!(name, Mode)`, which is
confined to the directory the program starts in, and a linear `File` with
partial `read!` and `write!` plus `close!`. Linux and WASI enforce the
confinement; sim65 checks names textually.

## Shape

Replace the single `Files` service with **directory capabilities**. That is
the Capsicum and WASI preopen model, and it gives a program as many roots as
it was granted:

```faun
Host.dir : Host -> Dir               # read-write, rooted where the program runs
Host.read_dir : Host -> ReadDir      # the same root, read-only

Dir.sub! : (Dir, Str) -> Result(Dir, OpenError)    # narrow to a subdirectory
Dir.read_only : Dir -> ReadDir                     # pure attenuation
```

- `Dir` and `ReadDir` are **unrestricted** when they come from the host: the
  root is a host-held descriptor that lives for the whole program. A `Dir`
  from `sub!` holds a descriptor, so it is linear and needs `close!`. The
  alternative, which avoids the obligation, is for `sub` to be pure and
  answer a (root, path prefix) pair, re-resolving the prefix on every open.
  That costs a longer path per call, but it drops the obligation and the
  syscall. **Lean: pure prefix.** Descriptor-backed subdirectories become an
  optimization the target may make internally.
- Authority is split by type, never by bits on a handle. `ReadDir` has
  `open_read!`, `list!` and `stat!`, and `Dir` has all of those plus creating,
  writing, removing and renaming.

## Names

- A name is a `Str` of `/`-separated components relative to a directory
  capability. `..`, a leading `/`, an empty component and NUL are refused
  before the host is called, as `[Escapes, InvalidName]`. The check is Faun
  code, shared by every target.
- Symlinks can't escape either. Linux uses `openat2` with `RESOLVE_BENEATH`.
  WASI enforces it itself. Windows resolves relative to a directory handle and
  checks the final path. A target that can't confine symlinks, such as sim65,
  treats them as unsupported. It never weakens the rule.
- **Names that Windows can't create** (`CON`, `aux.txt`, names with a trailing
  dot or space, `:`) are refused as `InvalidName` on Windows only. The
  portable contract says that which names are valid is a host property. A
  portable linter could warn about them everywhere.
- Case sensitivity and Unicode normalization are host properties too, and are
  documented, not emulated.

## Opening

A mode sum is simpler than a flags record, and each mode maps to one fixed
set of flags per target, as `flags(Mode)` already does:

```faun
ReadDir.open_read! : (ReadDir, Str) -> Result(Reader, OpenError)
Dir.open_write! : (Dir, Str, [Overwrite, Append, CreateNew]) -> Result(Writer, OpenError)
Dir.open_edit! : (Dir, Str, [Existing, CreateIfAbsent]) -> Result(File, OpenError)

OpenError : [NotFound, AlreadyExists, Denied, IsADirectory, NotADirectory,
             Escapes, InvalidName, NoSpace, Other(Nat)]
```

This splits `File` into `Reader`, `Writer` and `File` (read and write). The
split turns "wrote to a file opened for reading" into a type error instead of
an `EBADF`. All three are linear.

## Reading and writing

```faun
Reader.read! : (Reader, Nat) -> Result([Data(List(U8)), End], ReadError)
Reader.read_at! : (Reader, U64, Nat) -> Result([Data(List(U8)), End], ReadError)
Writer.write! : (Writer, List(U8)) -> Result(Nat, WriteError)
File.write_at! : (File, U64, List(U8)) -> Result(Nat, WriteError)
Writer.sync! : Writer -> Result({}, WriteError)
Reader.close! : Reader -> Result({}, [Other(Nat)])
Writer.close! : Writer -> Result({}, WriteError)       # consumes on both branches
```

- **Positional reads and writes are primary for random access.** `pread`/
  `pwrite`, WASI `fd_pread`, and `ReadFile` with an offset in `OVERLAPPED` are
  each one call. They have no cursor state, and they are what a database or
  an archive reader actually wants. Streams keep the cursor, because the
  kernel keeps it anyway.
- **`read!` and `write!` are partial.** `read_to_end!` and `write_all!` are
  Faun loops, as they are now.
- **Offsets are `U64`.** File sizes are bounded by the host, not by `Nat`, and
  the type says so.
- `sync!` is its own operation. Durability is never implied by `close!`.

## Namespace operations

```faun
ReadDir.stat! : (ReadDir, Str) -> Result(Stat, StatError)
ReadDir.list! : (ReadDir, Str) -> Result(List(Entry), ListError)
Dir.make_dir! : (Dir, Str) -> Result({}, [AlreadyExists, NotFound, Denied, Other(Nat)])
Dir.remove! : (Dir, Str) -> Result({}, [NotFound, NotEmpty, Denied, Other(Nat)])
Dir.rename! : (Dir, Str, Str) -> Result({}, RenameError)   # within one Dir: atomic replace

Stat : {kind: [File, Directory, Link, Other], size: U64, modified: [Known(Time), Unknown]}
Entry : {name: Str, kind: [File, Directory, Link, Other]}
```

- `list!` returns the whole directory as a list, in an unspecified order. The
  target loops over `getdents64` or `fd_readdir` internally. A streaming
  variant can come later; very large directories are rare, and a list keeps
  the API pure-shaped.
- Only `rename!` within one `Dir` promises atomicity. Renaming across
  capabilities might cross filesystems, so it is a separate operation or
  simply absent.
- Timestamps have host precision, and `Unknown` is an honest answer (FAT,
  some WASI hosts).

## Whole-file helpers (library, not host)

```faun
read_file! : (ReadDir, Str) -> Result(List(U8), ...)          # open, read_to_end, close
write_file! : (Dir, Str, List(U8)) -> Result({}, ...)         # write temp, sync, rename
```

`write_file!` is the atomic-replace idiom done right, once: write a temporary
sibling, `sync!`, then `rename!` over the target. It's Faun code over the
contract above, so every target gets it correct, and no host needs a
"write atomically" primitive.

## What is left out

- **A current working directory.** It is process-global mutable state. The
  starting directory is just the root `Dir`.
- **Absolute paths.** A tool that needs `/etc/hosts` is granted a `ReadDir`
  for `/etc` by its launcher, or uses a target-specific `host.root_dir` that
  only full-authority targets offer.
- **`mmap`.** A mapped file changes under the program when another process
  writes it, which breaks value semantics for a `List(U8)`. A target _may_
  use a private mapping to implement `read_file!` on a file it knows won't
  change, but that is the target's optimization, never a user-visible
  contract.
- **Locks, permissions, ownership, extended attributes.** These are
  Unix-specific or Windows-specific contracts, if they are ever needed.

## Mapping check

- **`open_read!`:** `openat2` (RESOLVE_BENEATH) on Linux, `path_open` on WASI
  preview 1, `NtCreateFile` with a root handle on Windows.
- **`read_at!`:** `pread64` on Linux, `fd_pread` on WASI preview 1, and
  `ReadFile` with an offset on Windows.
- **`list!`:** `getdents64` loop on Linux, `fd_readdir` loop on WASI preview
  1, `NtQueryDirectoryFile` loop on Windows.
- **`rename!`:** `renameat2` on Linux, `path_rename` on WASI preview 1,
  `SetFileInformationByHandle` on Windows.
- **`sync!`:** `fdatasync` on Linux, `fd_datasync` on WASI preview 1,
  `FlushFileBuffers` on Windows.

Each is one primitive per call, apart from the listing loop, which the
target owns because the platform's cursor is a detail Faun shouldn't see.
