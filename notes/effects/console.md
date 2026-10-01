# Console: args, environment, standard streams, exit

**Status: brainstorm.** What exists today is `Host : {args: List(Str)}` with
`exit!`, `stdin`, `stdout`, `stderr`, `print!`, `println!`, `run!` and
`run_stdin!` (`crates/faun/standard/hosts/*.fn`).

## Startup values

Startup values are fields on `Host`. The target produces a field only if the
program reads it, so an extra field costs nothing.

```faun
Host : {args: List(Str), raw_args: List(List(U8))}.( ... )
```

- **`args`.** Arguments as text, with the program's own name first. Unix
  arguments are bytes, Windows arguments are UTF-16, and WASI 0.2 and later
  already requires UTF-8. If an argument is not valid text, the target refuses
  to start and reports that on stderr, before `main!` runs. That is the one
  place a startup failure is allowed, and it only happens to a program that
  reads `args`.
- **`raw_args`.** Unix bytes, unvalidated, for tools such as `ls` that must
  handle any file name. A Windows target produces WTF-8 here. This field is
  optional: a target without raw arguments leaves it out.
- **Windows quoting.** Windows passes one command line, and each program
  splits it itself. The Windows target splits it by the Microsoft C runtime's
  rules (`CommandLineToArgvW`), which is what nearly every program uses.
  Document that, and don't invent another rule.

## Environment

The environment is ambient configuration, which is exactly what capabilities
exist to stop. Treat it as a snapshot capability:

```faun
Env : [Env].(
  get : (Env, Str) -> [Found(Str), Absent]
)
```

- `host.env` is a pure selector, and `get` is pure. The snapshot is taken
  once at startup and never changes, so no `!` is needed.
- **Allowlist where a launcher exists.** A WASI runtime passes only the names
  it was told to (`--env`). A native Linux binary has no launcher, so its
  target passes the real environment. Requirement reports should still say
  "reads the environment" so it can be audited.
- A value that isn't UTF-8 reads as `Absent` through `get`. A `get_raw`
  that answers bytes can come later if it is needed.
- There is no `set!`. A child's environment is given explicitly in its spawn
  spec (see [processes.md](processes.md)).

## Standard streams

`Stdin`, `Stdout` and `Stderr` are unrestricted services, not resources.
They are independently grantable: a library that logs can take `Stderr`
alone.

```faun
Stdin : [Stdin].(
  read! : (Stdin, Nat) -> Result([Data(List(U8)), End], ReadError)
)

Stdout : [Stdout].(
  write! : (Stdout, List(U8)) -> Result(Nat, WriteError)
)
```

Done (see [roadmap.md](roadmap.md)):

- **`End` instead of an empty list.** `read!` answers `Chunk`,
  `[Data(bytes), End]`, so the loop's exit is a tag, as Ori proposes.
- **Per-operation error rows.** `ReadError : [IsADirectory, Other(Nat)]` and
  `WriteError : [BrokenPipe, NoSpace, Other(Nat)]`. Neither carries
  `NotFound`.
- **Broken pipes are values, on every target.** Writing to a pipe nobody
  reads raises `SIGPIPE` on Linux, which ends the process by default. The
  Linux target ignores it before anything else runs in a program that
  writes, so the write answers `Err(BrokenPipe)`, as it does under WASI and
  Windows. That costs 25 bytes of code, hello world included.

  Why this over the alternatives:
  - **C** keeps the default: `| head` ends a program quietly, but control
    leaves from inside a write, with no `Result` and no cleanup. That is the
    surprise control flow Faun rules out, and it would make Linux the one
    target where a write can end the program.
  - **Go** splits by descriptor: a broken pipe on stdout or stderr ends the
    program, and on any other descriptor it is an error. Consistent within
    Linux, but still a write that ends the program.
  - **Rust**, **Python** and **Node** ignore the signal, as Faun does. Their
    known cost is `rust-tool | head` printing "failed printing to stdout:
    Broken pipe", because each program must handle the error. Faun's runners
    handle it for the common case: a runner whose output meets `BrokenPipe`
    finishes quietly with status one.

  What remains to watch:
  - A program that discards its write results keeps running after its
    reader is gone, until its loop ends. A warning for a discarded
    write `Result` would catch it.
  - An ignored signal is inherited, so the spawn code must restore the
    default in a child (see [processes.md](processes.md)).
  - Sockets need nothing more, but sending with `MSG_NOSIGNAL` keeps a socket
    write safe even in a program that never ignored the signal (see
    [network.md](network.md)).

Still proposed:

- **No buffering in the host.** Each `write!` is one `write` syscall, one
  `fd_write`, or one `WriteFile`. Buffering is a Faun value threaded through
  the program:

  ```faun
  out = Buffer.new(host.stdout, 65536)
  out = out.put!(line)      # flushes with one write! when the buffer fills
  done = out.flush!()
  ```

  `Buffer` holds only an unrestricted `Stdout`, so it isn't linear. A buffer
  around a `File` is linear by containment, and must be flushed and closed
  explicitly.

- **Windows consoles.** `WriteFile` on a console handle interprets bytes in
  the console code page. The Windows target sets the output code page to UTF-8
  at startup, or uses `WriteConsoleW` when the handle is a console. Either way,
  `Stdout` stays a byte stream.

## Terminals

A separate, optional contract. A pipe has no size, and a board has no
terminal:

```faun
Terminal : [Terminal].(
  is_terminal : (Terminal, Stream) -> Bool          # startup fact, pure
  size! : Terminal -> Result({columns: Nat, rows: Nat}, [NotATerminal])
  raw! : Terminal -> Result(Raw, [NotATerminal, Other(Nat)])
)

Raw : [Raw(Nat)].(
  restore! : Raw -> Result({}, [Other(Nat)])        # consumes
)
```

Raw mode is a good example of a resource that isn't a handle. It is a change
to shared state that must be undone, so `Raw` is linear and the checker
insists that `restore!` is reached on every path. This is exactly the bug
class (a crashed TUI leaves the terminal in raw mode) that RAII tries to
solve implicitly.

Implementation: `ioctl(TCGETS/TCSETS, TIOCGWINSZ)` on Linux, and
`GetConsoleMode`/`SetConsoleMode` with virtual-terminal processing on Windows.
WASI and sim65 omit it. Terminal output styling (colors, cursor movement) is
bytes on `Stdout` and belongs in a library.

## Exit

Exit statuses are less portable than they look:

- **Linux, macOS:** 0 to 255.
- **Windows:** a 32-bit code.
- **WASI 0.2+:** `result<_, _>` only; a numeric code is a later, unstable
  addition.
- **browser, board:** nothing; the program simply stops.

So split it:

```faun
exit! : (Host, [Success, Failure]) -> []       # every command target
exit_code! : (Host, U8) -> []                  # Unix-like and Windows targets
```

`U8` states the portable range in the type, so a code of 300 can't wrap to
44 by accident. A program that needs `exit_code!` compiles only where exit
codes exist.

Today's `exit! : (Host, U8) -> []` is the second of these under the first
one's name; the split is not made yet.

## Runners

`run!` and `run_stdin!` stay as Faun code in the host module: read what the
callback's shape asks for, call the pure function, print the answer, and exit.
A runner is where portability pays off most, because the application code is a
pure function and the runner is written once per target.
