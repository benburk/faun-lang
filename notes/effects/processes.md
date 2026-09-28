# Processes

**Status: brainstorm.** Nothing exists yet. Ori's notes put child processes
after files and networking, and name processes, not threads, as the nearer
route to using more than one core.

## Goals

- Spawn from a complete, explicit description. Nothing is inherited unless the
  description says so: no environment, no working directory, no open
  descriptors.
- A child is a linear resource, and a pipe is a linear resource. Reaping is an
  explicit `wait!`, never a finalizer.
- No `fork`. It can't be implemented on Windows, WASI or the browser, and it
  duplicates Faun's heap and linear resources. Spawn in the style of
  `posix_spawn` is what every platform actually has.
- The common case, "run this and collect its output", must not deadlock and
  must not need the reactor.

## The spec

A spawn spec is an ordinary Faun record. Its defaults come from a builder
function, since there are no default arguments:

```faun
Spec : {
  program: Program,
  args: List(Str),
  env: List((Str, Str)),        # the child's whole environment; empty by default
  dir: [Inherit, In(Dir)],      # the child's starting directory
  stdin: [Null, Pipe, Inherit(Stdin)],
  stdout: [Null, Pipe, Inherit(Stdout)],
  stderr: [Null, Pipe, Inherit(Stderr)],
}
```

- **`Program` is a capability-derived value, not a string.** Looking a name
  up on `PATH` depends on the ambient environment, so it's an explicit
  operation: `processes.find!(name) -> Result(Program, [NotFound])` searches
  the `PATH` the target was granted. `processes.at(dir, name)` names a binary
  inside a directory capability the program already holds. Either way, the
  authority to run programs is visible.
- `Inherit` carries the parent's stream capability, so a library that can't
  write to stdout can't give a child permission to either.
- **`args` quoting on Windows.** The target joins the list into one command
  line by the Microsoft C runtime's rules. That is correct for nearly every
  program, and documented as a host property for the rest (`cmd.exe` and
  batch files parse differently).

## API

```faun
Processes.spawn! : (Processes, Spec) -> Result(Child, SpawnError)

Child : [Child(Nat)].(
  wait! : Child -> Result(Exit, [Other(Nat)])        # consumes
  kill! : Child -> Result({}, [Other(Nat)])           # loans; wait! still required
)

Exit : [Exited(U32), Signaled(U8)]
SpawnError : [NotFound, Denied, NotExecutable, Other(Nat)]
```

- `Exited(code)` is portable. `Signaled` only happens on Unix targets, but it
  sits in the row everywhere, so a program that matches exhaustively is
  portable. A Windows target just never produces it.
- **Pipes.** Pipes come out of the child as separate linear resources, so
  they can be closed independently. The obvious spelling is for `spawn!` to
  answer a record:

  ```faun
  {child, stdin, stdout, stderr} = processes.spawn!(spec)?
  ```

  where each pipe field is `[Piped(PipeWriter), NotPiped]`. That is
  awkward to match. An alternative is three separate specs whose types follow
  the choice: `Spec(i, o, e)`, where choosing `Pipe` for stdout makes the
  result's `stdout` a `PipeReader`, and choosing `Null` makes it `{}`.
  Faun's structural records could carry this, with each stdio choice as its
  own type instead of a tag in a sum. **Open.**

## The common case: run and collect

Reading a child's stdout and stderr with blocking reads, one after the other,
deadlocks as soon as the child fills the other pipe. Every language
rediscovers this. The fix belongs in the host, because only the host can wait
on two descriptors at once without a reactor:

```faun
Processes.run! : (Processes, Spec, List(U8)) -> Result(Output, SpawnError)
Output : {exit: Exit, stdout: List(U8), stderr: List(U8)}
```

`run!` writes the given stdin, drains both outputs with `poll`, `ppoll` or
overlapped I/O, and reaps the child. Nothing linear escapes, so it's the
friendliest API for scripts. It is Rust's `Command::output`, but with stdin
included and no background thread.

## Linux mapping

- **Spawn:** `clone3` with `CLONE_VFORK | CLONE_VM | CLONE_PIDFD`, then
  `execve`. vfork semantics avoid copying the address space, and with no
  libc there is no `atfork` state to worry about. The child side of the
  clone only rearranges descriptors (`dup3`, `close_range`) and calls
  `execve`, and the target emits that code directly.
- **`SIGPIPE`.** A Faun program that writes ignores `SIGPIPE`, and an
  ignored signal is inherited across `execve`. The child side of the clone
  restores the default before `execve`, so a C program started from Faun
  still dies quietly under `| head` (see "Broken pipes" in
  [console.md](console.md)).
- **`Child` is a pidfd.** That makes it a descriptor like any other: `wait!`
  is `waitid(P_PIDFD, ...)`, `kill!` is `pidfd_send_signal`, and the reactor
  can wait on a child exiting with the same `poll` it uses for sockets. No
  `SIGCHLD` handler and no global reaping.
- The program is resolved relative to a directory descriptor with `execveat`,
  which keeps `Program` capability-relative.

## Other targets

- **macOS:** `posix_spawn`. The child is a pid, and the reactor waits on it
  with `kqueue`'s `EVFILT_PROC`.
- **Windows:** `CreateProcessW` with an explicit handle list. The child is a
  waitable process handle.
- **WASI:** none in 0.2 or 0.3, so the contract is omitted.
- **browser:** none (a Worker is not a process), so the contract is omitted.
- **sim65:** none, so the contract is omitted.

## Replacing the program

`exec!` replaces the current program, so its success type is the empty `[]`:

```faun
exec! : (Host, Spec) -> Result([], SpawnError)
```

It returns only on failure. Whether a linear resource may still be live at
the call is the same open question as for `exit!`. It is a Unix-only contract,
which is useful for
wrappers and shells, and it is honest about what it does: after it succeeds,
nothing in the program exists any more.

## Parallelism

Processes give coarse parallelism with no new language semantics. Each child
has its own heap, World and Host, and talks through pipes. A future
`worker` contract could spawn the _same_ program at another entry point, with
a typed channel instead of bytes, using the processes contract underneath.
Shared-memory threads remain out of scope, as in Ori.
