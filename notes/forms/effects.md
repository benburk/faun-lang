# Effects and resources

This note owns how a Faun program touches the world: effects marked by `!`
in a name, `Host` as the authority every effect needs, the order effects run
in, the rule that an effect stands on a line of its own, and linear
resources such as `File`, which must be used up exactly once. What each
host stream and error row holds is in the standard README; which host
modules to add next is brainstormed in [effects](../effects/README.md).

## Effects

An effect is a call of a name ending `!`. A definition that calls one is
named with `!` too; one without `!` is pure, and calling an effect from it,
or from a lambda, is refused:

```text
error: pure definitions cannot call effect `println!`
 --> greet.fn:3:16
  |
3 | greet(host) -> host.println!("hi")
  |                ^^^^^^^^^^^^^^^^^^^
```

An effect stands at the top of a line: as a binding's value, as a body, as
what a line's `if` or `is` tests, or on a line of its own, where what
it answers is thrown away. It never stands inside an argument, an operand,
a guard or the right of `&`, so the order effects run in is the order of
the lines. A line `call!()?` passes a failure on. Only an effect may stand
alone on a line; any other value is bound to a name.

```ruby
main! : Host -> []
main!(host) -> (
  host.println!("Hello, world!")
  host.exit!(0)
)
```

## Host

`main!` is handed the program's one `Host`, and is `Host -> []` whether or
not it says so. `Host`'s constructor is private to the target's host
module, mounted at `std.host`, so no program can make one. Every effect is
a method of `Host` or of something reached from it: `host.stdout`,
`host.stdin`, `host.stderr` and `host.files`, each a value of its own type
that can be handed on alone. `host.args` is an ordinary field.

```ruby
main!(host) -> (
  copied = copy!(host.files, host.stdout)
  host.exit!(status(copied))
)
```

(`crates/faun/examples/files/copy.fn`.) `copy!` can open files and write
to standard output, and nothing else. A definition with no clauses, whose
answer the target supplies, may be written only in a host module.

Effects run in the order written. Barb, the core every program is lowered
to, keeps the order and number of calls to anything bodyless, and the path
each is made on; there is no world value threaded beside them. Pure work
may move across an effect, or be left out where nothing reads it.

`exit! : (Host, U8) -> []` ends the program with a status. `[]`, the empty
tag row, has no values, so `exit!` never answers, and `main!` answering
`[]` ends every path in a call that never answers: `exit!`, or one of the
runners, `run!` and `run_stdin!`, which hand a pure function its input,
print its answer and finish.

## Resources

A `File` is a resource: whatever opens one must use it up exactly once on
every way it goes on, by closing it or by answering it to something that
does. Dropping one, using one after it is closed, and leaving by `?` while
one is held are each refused.

`?` closes nothing, so a file is closed before `?` is asked of what reading
it answered:

```ruby
measure! : Files -> Result(Nat, IoError)
measure!(files) -> (
  source = files.open!("input.txt", Read)?
  counted = size!(source)
  closing = source.close!()
  n = counted?
  closed = closing?
  Ok(n)
)
```

Nothing is written to say what a function does with a file it is handed.
One that only reads it, writes it, or hands it on to what does the same
lends it, and may leave by `?`, since its caller still holds the file:

```ruby
size! : File -> Result(Nat, IoError)
size!(file) -> (
  bytes = file.read_to_end!()?
  Ok(bytes.len())
)
```

One that closes or answers it on every way it goes on takes it. One that
does one on some ways and the other on others is refused. A type holding a
file, such as `List(File)` or `Result(File, OpenError)`, is a resource too.
A test or arm that names the file in its pattern takes the value apart; the
standard README's resource paragraphs say how records and failed tests
hold one.

What makes `File` a resource is the target's declaration that closing a
descriptor uses up what it is handed. `Host`, `Stdout` and `Files` have no
such routine and may be copied and passed freely.

## Open questions

The README leaves two questions open:

- **FFI.** How a program reaches a C library. The archived
  [host interface draft](../archive/rfcs/drafts/host-interface.md) and
  [bindings](../effects/bindings.md) sketch wrapping one behind a
  Faun-native host module, with no pointers in the language.
- **Concurrency.** Nothing is built. The [events](../effects/events.md)
  brainstorm leans to a reactor the host drives, as Ori's design did,
  rather than threads or `async`.

## Rationale

### Why `!` in the name?

So a reader sees every effect where it is called, and the compiler can
check purity from a name alone. A pure definition is then one whose calls
may be shared, reordered or left out, and the optimizer relies on that.
Since effects stand one to a line, evaluation order inside an expression
is never observable.

The mark is one bit: a signature says that a definition may do something,
not what. The capabilities it is handed say what it can reach, and that is
the finer record. Writing a set of effects into every type would change
every caller's signature when a callee gains one.

### Why capabilities, and no ambient authority?

A program can touch only what it was handed. There is no global stdout or
file system to name, and importing a module grants nothing, so a library
handed `Stdout` cannot open a file. Authority is not a feature of its own:
it is a value of a type whose constructor is private, and narrowing it is
passing a field. A target supplies only what a program reaches, so a
program that never reads `host.args` makes its target produce nothing.

The cost is that an effectful helper deep in a program needs its
capability passed down every call on the way. Pass the narrowest one, as
`copy!` takes `Files` and `Stdout` rather than `Host`.

### Why no effect handlers, IO monad, effect polymorphism or `async`?

Each needs functions as values, and Faun's are second class: a callback is
passed straight into a call and never held, and a lambda is pure.

- **Handlers** capture the rest of a computation as a continuation, a
  suspended function value that Faun has no way to hold, and would have to
  say how a linear file inside one is copied.
- **An IO monad** sequences effects where the compiler cannot. Faun's
  compiler already keeps their order, and a monad needs higher-kinded types
  and suspended computations, neither of which Faun has.
- **Effect polymorphism** ranges over an unknown effectful callee, and
  there is none: every effectful call names its callee.
- **`async`** would split every function in two. How Faun does concurrency
  is open.

The cost is that a library cannot take an effectful callback: no
`with_file!(path, use!)` and no effectful `map`. The recourse is a
recursive `!` definition, whose lines may do effects.

### Why linear resources instead of destructors or RAII?

Closing is an effect: it is observable and can fail. `close!` answers
`Result({}, CloseError)`, and that row holds `NoSpace`: a write the target
accepted can still be found not to fit when the file is closed. A
destructor run at the end of a scope would be a hidden call with nowhere to
put its error. Many resources also have more than one way to finish:
flush or discard, wait or kill, commit or roll back. Choosing one is the
program's policy, not the compiler's.

Memory is different: releasing a value runs no program code, cannot fail,
and chooses nothing, so the compiler frees memory implicitly
([memory](../machine/memory.md)) and never closes a file. The cost is one
explicit close on every way a function goes on, which the checker points
to where it is missing.

### Why are loans inferred, with no borrow syntax?

Every effectful call names its callee, effectful functions are never
values, and the only way to keep a file past a call is to answer it, which
is taking it. So the compiler
knows, at every call, whether the callee lends or takes each file, by
reading its body, and nothing a borrow syntax would say is unknown. A loan
lasts for its call: there are no references and no lifetimes.

Ori first threaded the handle through every call, `read!` answering the
file back beside its result, which stranded the file wherever `?` left and
filled helpers with `file2` and `file3`. The cost of inference is that
whether a function lends or takes is part of its interface without being
written in its signature.

### Why does `?` close nothing?

`?` passes an `Err` on, in pure code and effectful alike. If it closed
what was held, a visible early return would hide effects, and their errors
would have nowhere to go, nor would it be clear which close to make or
which error wins. Instead, leaving by `?` while a file is held is refused,
and the message says to close first and ask `?` after, as `measure!` does.
A helper that only lends a file uses `?` freely.

### Why is exit `exit!`?

Ending a program is observable: the status is what a shell or a test
harness reads. So it is an effect, needs `Host`, and stands where effects
do. Its answer, `[]`, says that nothing follows it, and an entry answering
`[]` makes every way out of `main!` an effect rather than an implicit
return status. The status is a `U8` because a byte is all every target
keeps: Linux reports only the low eight bits, so a status worked out from a
`Nat` says how it is cut down, `U8.of_nat(n)`.

### Why not refuse an effect's answer dropped on a line of its own?

An effect alone on a line throws away what it answers, so
`host.stdin.read_to_end!()` there drops a `Result`, and a failed read goes
by unseen. Refusing that, and asking for `_ = call!(…)` wherever an answer
other than `{}` or `[]` is dropped, was weighed and rejected: it would cost
every program that prints, where it would catch little.

- **Printing answers a `Result`,** since a write can fail, so every print on
  a line of its own would need `_ =`, hello world first. `main!` answers
  `[]` and cannot pass the failure on with `?`. A marker on every print
  stops marking anything: a `_ =` before a write to a file that matters
  would look like all the others.
- **A debugging print** would need `_ =`, or a `?` its function's error
  type may not hold.
- **A print added to a function with a closed error row** and passed on
  with `?` puts `WriteError` in that row and in every caller's above it, as
  a checked exception does.

Making printing answer `{}`, the host ending the program on a failed write
as Python does on a broken pipe, would keep every print as written, but
printing would be the one effect whose failure no program can see, and a
program writing a report it must not lose could not tell it was lost. A
warning in place of a refusal is not on offer: every diagnostic refuses.

The cost is that a dropped `Err` stays silent. Every effect ends in `!`, so
the recourse is grep, review, or a lint for `!` lines whose answer is a
`Result` ([lints](../lints.md)); a line `call!()?` passes its failure on
instead.

## History

- **2026-10-04:** refusing an effect's dropped answer was proposed and
  rejected the same day. Settling whether `&` on `Bool` should
  short-circuit led to writing down that effects stand one to a line, which
  was already enforced in all but this one form. A sketch carrying a
  `discarded` flag from the syntax tree into the checker refused about forty
  tests, nearly all through the one printing line in the runner `faun test`
  generates for expectations, beside eleven printing lines in the corpus.
  The same day a line `call!()?` was allowed to stand on its own.
- **2026-11-10:** loops were removed ([iteration](../iteration.md)), so an
  effect is no longer tested by one, and an effectful walk is a recursive
  `!` definition.

## Related

- [Pattern matching](pattern-matching.md): tests and arms that take apart a
  value holding a file
- [Memory](../machine/memory.md): reference counting, which frees memory
  implicitly where resources must be closed explicitly
- [Architecture](../machine/architecture.md): bodyless calls, and how Barb
  keeps their order
- [Values and functions](../values/functions.md): second-class callbacks,
  which rule out effectful ones
- [Host effects brainstorm](../effects/README.md) and
  [roadmap](../effects/roadmap.md): host modules to come
- [Lints](../lints.md): lines whose dropped answer is a `Result`
