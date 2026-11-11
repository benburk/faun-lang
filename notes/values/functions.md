# Functions

This note owns how Faun writes and passes functions: definitions as a
signature and clauses, values written `name = value`, lambdas, and
callbacks, which are passed into a call and never held. What a clause's
patterns match belongs to [pattern matching](../forms/pattern-matching.md),
and a type's own functions to [methods](../forms/methods.md).

## Definitions

A definition is an optional signature and one or more clauses. A clause is
a head of patterns, an optional guard, `->`, and a body: one expression, or
a block of lines in parentheses.

```ruby
gcd : (Nat, Nat) -> Nat
gcd(a, 0) -> a
gcd(a, b) -> gcd(b, a % b)
```

A function type writes its parameters in parentheses, `(Nat, Nat) -> Nat`,
or one alone, `Nat -> Nat`. Without a signature the type is inferred, `where`
bounds and all; [types](../types.md) owns inference and `_` in signatures.

Calls are uncurried: a call hands over every argument at once. `add(1)` for
an `add` of two parameters says "`add` takes 2 arguments, but 1 was given",
with help that there is no partial application, and `n.max(2, 3)` says
"`max` takes 1 argument, but 2 were given". There are no default, named or
variadic arguments: `add(a: 1, b: 2)` does not parse.

## Values

A definition of no parameters is a value, written `name = value` and used
by its name alone, at the top level or in a type's block:

```ruby
solar_mass : F64
solar_mass = 4.0 * F64.pi * F64.pi
```

`zero() -> 0` is refused with "a definition of no parameters is a value:
`zero = ...`", and `zero()` with "`zero` is a value, not a function". The
same holds for a type's value, `Vec3.zero`, and for one a `where` bound
gives, `a.zero` where the bound is `a.zero : a`. The head is one name: a
pattern before `=` is refused, and so is an effect's name, since a value is
no effect. A value's expression may start on the line after `=`, as a body
may after `->`. Below name resolution a value is still a definition of no
parameters, and a use of it is a call.

## Lambdas

A lambda is `|patterns| body`, and stands only as a call's argument. It
takes one parameter or more, each a pattern that matches whatever it is
handed, so a tuple or record may be taken apart but `(1 | 2)` is refused.
Its body is an expression or a block:

```ruby
summed : List(Nat) -> Nat
summed(xs) -> xs.fold(0, |total, x| (
  doubled = x * 2
  total + doubled
))
```

A lambda reads the names around it. Its own `=` binds only its own names:
assigning `total = total + x` to a name of the body around it is refused,
since whatever calls the lambda may call it any number of times. `?` inside
a lambda answers the lambda, not the clause it is written in:

```ruby
doubled : List(Str) -> Result(List(Nat), [Malformed])
doubled(texts) -> texts.try_map(|text| Ok(Nat.from_str(text)? * 2))
```

A lambda handed to a pure
definition is pure: `names.map(|name| host.println!(name))` is refused, as
`map` calls no effect ([effects](../forms/effects.md)).

## Callbacks

A parameter may have a function type, and a call passes a named function, a
constructor, or a lambda there. Calling the parameter calls what was passed:

```ruby
bumped : (List(Nat), Nat -> Nat) -> List(Nat)
bumped(xs, f) -> xs.map(|x| f(x) + 1)

double : Nat -> Nat
double(n) -> n * 2

expect bumped([1, 2], double) == [3, 5]

wrapped : List(Nat) -> List(Result(Nat, [Bad]))
wrapped(xs) -> xs.map(Ok)
```

Functions are second-class: a function is passed straight into a call and
goes nowhere else. Each of these is refused:

| Written                             | Refused because                     |
| ----------------------------------- | ----------------------------------- |
| `f = twice`, `fs = [double]`        | a function cannot be bound          |
| `pick : Bool -> (Nat -> Nat)`       | a function is not answered          |
| `Handler : [Handler((Nat -> Nat))]` | data may not store functions        |
| `inc = \|x\| x + 1`                 | a lambda stands only as an argument |
| `True.select(twice, half)(3)`       | `select` would hold the function    |

The last is caught after specialization, where `select`'s type variable is
filled with a function and its body would answer one.

### How a callback is compiled

Every function value is known where it is passed: a definition, a
constructor, a lambda written there, or a callback the caller was handed in
turn. So a definition taking a function is made once for each set of
callbacks it is called with, and calling its parameter becomes a direct
call of the callback. A lambda becomes a definition of its own, taking what
it reads from where it was written ahead of its parameters. No function
value is left at run time, and no closure is built.

In `bytes.count(|byte| ['a', 'e'].contains(byte))`, `count` hands its work
to `count_from`, which is made for this lambda alone: the callback
parameter is gone, and the membership test stands where the call of it was.
A second `count` with another lambda gets a second `count_from`;
`faun emit barb` shows both.

### What cannot be made

A recursive call that wraps the callback it was handed in a new lambda
would need a new definition every time round, so it is refused at the
lambda:

```ruby
nest : (Nat, Nat -> Nat) -> Nat
nest(0, f) -> f(0)
nest(Succ(n), f) -> nest(n, |x| f(x) + 1)
```

```
error: this lambda wraps the callback it was handed and hands itself on
  = note: each round would ask for another definition, without end
  = help: recurse on data that says what to call instead
```

Wrapping a callback once is fine: `twice(n, f) -> apply(n, |x| f(f(x)))`
builds. Only the chain that grows each round is refused. The data that says
what to call is a type of its own:

```ruby
Wrap : [Plain, Plus1(Wrap)].(
  call : (Wrap, Nat -> Nat, Nat) -> Nat
  call(Plain, f, x) -> f(x)
  call(Plus1(inner), f, x) -> inner.call(f, x) + 1
)

nest : (Nat, Nat -> Nat, Wrap) -> Nat
nest(0, f, wrap) -> wrap.call(f, 0)
nest(Succ(n), f, wrap) -> nest(n, f, Plus1(wrap))
```

## Rationale

### Why are functions passed but never held?

Because then every call is direct. A held function is a closure: a record
of what it captured, allocated, reference-counted, and called through an
indirect jump that the optimizer cannot see past. A passed function is
known at its call site, so specialization copies the callee for it and the
optimizer reads the callback's body as if it were written in place. Range
analysis, inlining and the recognition of known shapes, such as a list's
`len`, all work on code they can see.

It also keeps every value first-order data. A value holding no function has
an equality, an order, a text and a hash that follow from its type, which
is how structural records, tuples and tags get them without being asked
([methods](../forms/methods.md)). Resource checking and pattern compiling
run on a program with no function values in it, and every target is handed
a first-order IR ([architecture](../machine/architecture.md)).

Faun tried the other way first. Every function value of one type was a
constructor of one closure type, and every call of a function parameter
went through one `apply` matching on it, so `count` called `apply` rather
than the lambda it was handed. Specializing per callback set replaced that,
and the closure types and their lowering went.

The cost is real. A callback cannot be kept in a record, a combinator
cannot return a function, and a list cannot hold behaviours. The
rock-paper-scissors arena (`examples/rps-arena`) shows the price: its
`play` is generic over any two player types through a `where` bound, but a
tournament needs a list, so every bot is a constructor of one sum `Bot`
whose methods forward to each bot's own. The recourse for a table of
functions is a sum of commands and a method that runs one:

```ruby
Op : [Double, Add(Nat)].(
  run : (Op, Nat) -> Nat
  run(Double, n) -> n * 2
  run(Add(k), n) -> n + k
)

expect [Double, Add(3), Double].fold(1, |n, op| op.run(n)) == 10
```

Unlike a list of closures, the sum can be compared, printed and matched
exhaustively. Each callback set also costs a copy of the definition that
takes it, so code grows with the number of distinct callbacks a program
passes.

### Why refuse a callback wrapped anew each round?

Specialization makes one definition per set of callbacks, and the wrapped
callback is a new set each round: the lambda holds the callback it was
handed, which held the one before. Making them would never finish. This is
not a check that the program stops, which Faun does not make
([computation](../computation.md#why-not-check-termination)); that
decision kept this one refusal because it is about what can be compiled, not about stopping. The
recourse is to recurse on data, as `Wrap` does above: the chain becomes a
value the program builds, and one `call` walks it.

### Why no currying or partial application?

A partially applied function is a held function: `add(1)` would be a
closure over the `1`. Beyond that, a definition has one arity. A method is
found by its receiver and called with all its arguments, a `where` bound
names a member with its whole type, `a.add : (a, a) -> a`, and a call that
leaves an argument out is an error at that call, rather than a function
value flowing on to fail somewhere else. The recourse is a lambda that says
what it fixes, `xs.map(|x| add(1, x))`, at the cost of point-free style.

### Why no default, named or variadic arguments?

The same single arity: every call states every argument, so a call is read
the same way by the reader, by specialization and by method resolution.
Records cover the cases these features serve. A record parameter names its
arguments, a record update supplies defaults, and a list takes any number:

```ruby
Layout = {width: Nat, indent: Nat}

plain : Layout
plain = {width: 80, indent: 2}

columns : Layout -> Nat
columns({width, indent}) -> width - indent

expect columns({indent: 4, *plain}) == 76
expect [3, 4, 5].sum() == 12
```

The cost is noise at the call: a record literal is longer than keyword
arguments, and a field left out is a type error rather than a default.

### Why are values not nullary functions?

Nothing else in Faun is a function of nothing: a lambda takes at least one
parameter and a function type at least one type. Faun is pure, so whether a
value is worked out once or at each use cannot be told. The corpus had 178
such definitions, constants and each type's `zero` or `empty`, all written
and used with `()` at every use, and defined with a head naming parameters
it does not have. An effect cannot hide behind the notation, since a value's
name takes no `!`.

The cost is that a value cannot be a function: `f = |x| x` does not parse,
since a lambda stands only as an argument, and `f = g` is refused, as
binding a function always was. Moving to values changed every program at
once, which a script did.

### Why not keep `name()`, or allow both?

Keeping `name()` costs `()` at every use of every constant, and reads as a
function of nothing. Allowing both would give one thing two spellings, and
the change was small enough to make whole. Working values out once at load
was also weighed: it means nothing different in a pure language, and a
compile-time constant is already folded.

### Why may a lambda not assign the names around it?

A lambda is called by the definition it is handed to, as many times as that
definition likes, perhaps none. An assignment to a name outside it would
have no single meaning after the call. The lambda answers the new value
instead, and the code around it assigns:
`total = xs.fold(total, |t, x| t + x)`.

## History

- **2026-10-02:** values, proposed, approved and built the same day. Until
  then a constant was a definition of no parameters, `pi() -> 3.14159`, used
  as `pi()`, `Vec3.zero()` and `a.zero()`. The corpus held 178 such
  definitions in 59 files; comparing n-body with the branching draft, whose
  `solar_mass`, `days_per_year`, `bodies` and `system` are constants,
  prompted the change. Rewriting the type-qualified uses needed the list of
  types' values, since `False.not()` is a method call on a constructor.
- **2026-11-10:** loops were removed ([iteration](../iteration.md)), and
  with them the refusal of `continue` and `break` in a lambda written
  inside a loop's body.

## Related

- [Types](../types.md): inference, `where` bounds, and specialization by type
- [Methods](../forms/methods.md): functions in a type's block, and derived
  members
- [Pattern matching](../forms/pattern-matching.md): clause heads, guards
  and coverage
- [Computation](../computation.md): strict evaluation, and why stopping is
  not checked
- [Effects](../forms/effects.md): `!` definitions and capabilities
