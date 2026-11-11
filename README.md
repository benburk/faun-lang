# Faun

A work-in-progress compiled, strict functional language exploring whether C-like performance, Python-like concision, and Rust-like safety can be obtained from a comparatively small set of language mechanisms.

```ruby
# Computes the factorial of an arbitrarily large natural number.
# Panic free: every match covers every input.
factorial : Nat -> Nat
factorial(0) -> 1
factorial(m) -> m * factorial(m - 1)

# Effectful functions come from the host, and end with an exclamation mark
main!(host) -> (
  name = host.args.get_or(1, "world")
  host.println!("Hello, ${name}!")
  host.exit!(0)
)
```

- **Strict functional semantics**: immutable values, value semantics, algebraic data types, pattern matching, and eager evaluation.
- **Static, decidable typing**: HM-style type inference with row-polymorphic structural types; type signatures are optional, and may leave any part to inference with `_`.
- **A pure core defined for every input**: pattern matches must be exhaustive. Recursion is not checked to stop: a call whose answer is needed and never comes back hangs, and pure work nothing needs may be left out. Effects enter explicitly through host-provided capabilities.
- **Immutable semantics, mutable implementation**: heap values are reference-counted; uniquely owned storage may be reused in place when observationally equivalent to allocating a fresh value, with copy-on-write as the fallback.
- **Second-order functions without runtime closures**: functions may accept statically known function arguments and call-site lambdas, but functions are not general runtime values.
- **Explicit effects and resources**: effectful operations are syntactically marked, capabilities are passed explicitly, and linear resource types enforce explicit acquisition, use, and cleanup.
- **Backend-independent semantics**: source programs expose neither machine layouts nor target intrinsics. Backends consume a shared, first-order machine-level IR.

Faun is equally defined by the features it does not have

- No source-level mutation, pointers, references, borrow syntax, or lifetime annotations.
- No tracing garbage collector, reference cycles, or manual memory management.
- No hidden semantic control flow: function and host calls happen only where written. There are no implicit constructors, destructors, exceptions, coercion hooks, or cleanup callbacks. Resource cleanup is explicit and statically enforced by linear resource types.
- No null or unchecked partial pattern matches.
- No inheritance, nominal subtyping, or implicit type conversions.
- No first-class closures, currying, or higher-kinded types.
- No dependent types or user-written proofs.
- No macros, runtime reflection, or general compile-time metaprogramming.
- No source-level object layouts, calling conventions, target intrinsics, or inline assembly.
- No dependency on LLVM or libc.
- And so much more! (That it doesn't have...)

## What works today

Three backends

- x86-64 Linux
- wasm32 WASI
- MOS 6502 sim65

Programs, in [`crates/faun/examples`](crates/faun/examples)

- Advent of Code 2015, days 1 to 19
- n-body and spectral norm benchmarks
- files read, written and closed, each checked to be closed once
- libraries: JSON, MD5, a command-line parser, a heap, graphs, templates, property tests and more
- `expect` tests, run by `faun test`

Editors

- Helix highlighting, by the tree-sitter grammar in [`editors/tree-sitter-faun`](editors/tree-sitter-faun/README.md)

## Examples

Newton's method, from [`newton.fn`](crates/faun/examples/newton.fn): functions passed by name, a guard, and a failure that is a value

```ruby
Func = F64 -> F64

# Newton's method, giving up after `n` steps: a root it never reaches is an
# error value, not a crash.
newton : (Func, Func, F64, Nat) -> Result(F64, [NoConvergence])
newton(_, _, _, 0) -> Err(NoConvergence)
newton(f, _, x, _) if f(x).abs() < 1.0e-12 -> Ok(x)
newton(f, df, x, n) -> newton(f, df, x - f(x) / df(x), n - 1)

f : Func
f(x) -> x * x - 2.0

df : Func
df(x) -> 2.0 * x

expect newton(f, df, 2.0, 50).ok_or(0.0).to_fixed(12) == "1.414213562373"
expect newton(f, df, 0.0, 50) == Err(NoConvergence)
```

Quicksort, from [`quicksort.fn`](crates/faun/examples/quicksort.fn): a generic function over any ordered type, list patterns, and lambdas

```ruby
sort : List(a) -> List(a) where Ordered(a)
sort([]) -> []
sort([pivot, *rest]) -> (
  smaller = rest.filter(|x| x < pivot)
  larger = rest.filter(|x| x >= pivot)
  sort(smaller).concat([pivot]).concat(sort(larger))
)

expect sort([3, 1, 4, 1, 5, 9, 2, 6]) == [1, 1, 2, 3, 4, 5, 6, 9]
expect sort(["pear", "fig", "apple"]) == ["apple", "fig", "pear"]
```

## Open design questions

- How to do FFI
- How to do concurrency
