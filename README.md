# Faun

A work-in-progress compiled, strict functional language exploring whether C-like performance, Python-like concision, and Rust-like safety can be obtained from a comparatively small set of language mechanisms.

```ruby
# Computes the factorial of an arbitrarily large natural number.
# Proven total and panic free.
factorial : Nat -> Nat
factorial(0) -> 1
factorial(m) -> m * factorial(m - 1)

# Effectful functions come from the host, and end with an exclamation mark
main!(host) -> host.println!("factorial(5) = ${factorial(5)}")
```

- **Strict functional semantics**: immutable values, value semantics, algebraic data types, pattern matching, and eager evaluation.
- **Static, decidable typing**: HM-style type inference with row-polymorphic structural types; type signatures are optional.
- **A total pure core**: pattern matches must be exhaustive, and recursive definitions are accepted only when the compiler can establish termination. Effects enter explicitly through host-provided capabilities.
- **Immutable semantics, mutable implementation**: heap values are reference-counted; uniquely owned storage may be reused in place when observationally equivalent to allocating a fresh value, with copy-on-write as the fallback.
- **Second-order functions without runtime closures**: functions may accept statically known function arguments and call-site lambdas, but functions are not general runtime values.
- **Explicit effects and resources**: effectful operations are syntactically marked, capabilities are passed explicitly, and linear resource types enforce explicit acquisition, use, and cleanup.
- **Backend-independent semantics**: source programs expose neither machine layouts nor target intrinsics. Backends consume a shared, first-order machine-level IR.

Faun is equally defined by the features it does not have

- No source-level mutation, pointers, references, borrow syntax, or lifetime annotations.
- No tracing garbage collector, reference cycles, or manual memory management.
- No implicit cleanup or hidden control flow: no constructors, destructors, RAII hooks, exceptions, or other user-defined code that runs implicitly. Resource lifetimes are explicit and checked with linear types.
- No null or unchecked partial pattern matches.
- No inheritance, nominal subtyping, or implicit type conversions.
- No first-class closures, currying, or higher-kinded types.
- No dependent types or user-written proofs.
- No macros, runtime reflection, or general compile-time metaprogramming.
- No source-level object layouts, calling conventions, target intrinsics, or inline assembly.
- No dependency on LLVM or libc.
- And so much more! (That it doesn't have...)

## What works today

Four backends

- x86-64 Linux
- AArch64 macOS
- wasm32 WASI
- MOS 6502 sim65

Programs

- exit(0)
- hello world
- simple arithmetic expressions

```ruby
main!(host) -> host.println!("Hello, world!")

gcd : Nat Nat -> Nat
gcd(a 0) -> a
gcd(a b) -> gcd(b a % b)

fib : Nat -> Nat
fib(0) -> 0
fib(1) -> 1
fib(n) -> fib(n - 1) + fib(n - 2)

factorial : Nat -> Nat
factorial(0) -> 1
factorial(m) -> m * factorial(m - 1)
```
