# Faun

A work-in-progress compiled, statically typed, functional programming language,
targeting x86-64 Linux, AArch64 macOS, wasm32 WASI, and MOS 6502 sim65.

The primary frontend implements an in-progress Ori-compatible language. The
`faun` command loads modules, parses, links, resolves names, infers polymorphic
types, and resolves methods in the current subset:

```sh
cargo run -- check crates/faun/examples/frontend.fn
cargo run -- check crates/faun/examples/literals.fn
cargo run -- check crates/faun/examples/utilities.fn
cargo run -- check --target x86_64-linux crates/faun/examples/main.fn
cargo run -- build --emit barb --target x86_64-linux crates/faun/examples/main.fn
cargo run -- build --emit machine --target x86_64-linux crates/faun/examples/main.fn
cargo run -- build --target x86_64-linux crates/faun/examples/main.fn
cargo bench -p faun --bench frontend
```

It supports package interfaces, nominal types and method blocks, closed records,
clauses, guards, lists, strings, literals, calls, methods, and operators. It performs
Hindley–Milner inference across recursive definition groups, instantiates
polymorphic signatures and constructors, and chooses nominal methods from the
receiver type. Parsed `where` constraints are not checked yet.

Applications define a bodyful `main! : Host -> []` and import their target-selected
interface from `std.host`. The empty structural variant type `[]` has no values,
so it marks computations that cannot return. `Host` currently contains immutable
`argc: Nat`; its constructor stays private, while `exit! : Host Nat -> []` carries authority
explicitly. Barb keeps `main!(host: Host)` as the entry and preserves ordinary
record projection. Machine lowering represents the current one-field `Host`
transparently; each target constructs it from its process startup convention.

Lowering monomorphizes reachable globals and data types, compiles clause and
record patterns, and defunctionalizes global functions, constructors, and
capturing lambdas. Literal expansions remain ordinary Barb operations. Ranges,
interpolated strings, local destructuring bindings, nonempty structural variants,
record updates and rows, and locally let-polymorphic values are not lowered yet. See the [frontend status and benchmark contract](notes/frontend.md) for the exact boundary.

The source frontends are separate crates. `faun` owns the primary language:
syntax, inference, module loading, lowering, and its standard package.
`faun-simple` owns the archived syntax and standard sources. Both lower into
`faun-core`, which owns Barb, machine IR, analysis, and the target interface.

`faun-driver` is the reusable source-to-artifact command driver. The `faun-cli`
package supplies the small official executable that registers the four bundled
target crates. A custom target can depend on `faun-driver`, register its target
and source host module, and obtain the same `check`, `build`, and `run` commands,
including `build --emit barb|machine`, without modifying the official executable:

```rust
use faun_driver::Backend;
use my_faun_target::MyTarget;

const BACKENDS: [Backend; 1] = [Backend::external(
    &MyTarget,
    concat!(env!("CARGO_MANIFEST_DIR"), "/host.fn"),
    true,
)];

fn main() -> std::process::ExitCode {
    faun_driver::run(&BACKENDS)
}
```

The archived `faun-simple` command validates definitions, runs a bounded optimization
schedule, recognizes arithmetic structurally, derives ranges, and lowers to
validated machine IR. Targets then prepare representations, check their limits,
and emit. A reference machine-IR interpreter supports 16-, 32-, and 64-bit
configurations.

See the [primary standard package](crates/faun/standard/README.md) and
[simple standard sources](crates/simple/standard/README.md). The simple
frontend has no automatic prelude or import syntax: prepend the needed library
files explicitly.

[Runtime naturals](notes/runtime-naturals.md) work on x86-64 and wasm32 using a
reusable private heap, 64 KiB by default; exhaustion exits with status 2 rather
than wrapping. Native AArch64 macOS and 6502 runtime naturals remain disabled
while those backends have narrower implementation limits. Fixed-width values
wider than a target word are still rejected.

`U8` and `Int` enforce their invariants structurally and support pure compile-time
uses after folding and dead-binding cleanup. Runtime product/sum packing and
signed lowering are not implemented.

Compiler clients should use `faun_core::targets::Target::compile`, or use
`Target::prepare` to inspect the prepared IR. Raw `emit` does not legalize
naturals or establish its validation
and target-acceptance preconditions. See [machine IR contracts](notes/machine-ir.md)
for external declarations, function construction, and representation rebuilding.

## Trying the AArch64 macOS baseline

The first macOS slice supports `exit!`, `argc!`, and writing static data. It emits
an ad-hoc-signed Mach-O that loads through `/usr/lib/dyld`, but imports no symbols
and links no libraries; output and termination use raw Darwin syscalls.

Build on another host, copy the executable, and run it on an Apple Silicon Mac:

```sh
cargo run --bin faun-simple -- build --target aarch64-macos \
  -o /tmp/faun-exit crates/simple/examples/exit.fn
scp /tmp/faun-exit your-mac:/tmp/faun-exit
ssh your-mac 'chmod +x /tmp/faun-exit; /tmp/faun-exit; echo $?'
```

The backend currently rejects internal functions, arithmetic, mutable globals,
and heap allocation before emission. This keeps `exit(0)`, `exit(argc)`, and
hello-world programs as explicit baselines while instruction lowering grows.

## Simple frontend literals and input

[`crates/simple/examples/hello.fn`](crates/simple/examples/hello.fn) is a complete
source program:

```text
main!(host) -> host.print!("Hello, world!\n")
```

Run it on the native backend with
`cargo run --bin faun-simple -- run crates/simple/examples/hello.fn`. A string
literal is UTF-8 and accepts `\n`, `\r`, `\t`, `\"`, `\\`, and `\'` escapes.
`host.print!(text)` is method-call syntax for `print!(host text)`; it writes a
static literal and completes the program with status zero. Strings do not yet
have a runtime representation, so they cannot be passed through user functions
or computed at runtime.

Decimal, hexadecimal, and binary natural literals are arbitrary precision:

```text
main!(host) -> host.exit!(0x2a)
```

A natural literal requires a declared `Nat` with the usual empty/successor
shape. It is stored compactly rather than expanded into a constructor chain.
There is no automatic prelude yet, so programs using numbers still prepend
[`crates/simple/standard/nat.fn`](crates/simple/standard/nat.fn).

String literals are useful but deliberately narrow. They may be bound locally
and passed directly to `print!`, but there is no concatenation, indexing,
length, UTF-8 traversal, runtime construction, or interpolation. In particular,
`"answer: ${answer}"` contains those dollar and brace characters literally.
Passing a string through a user function is rejected because `Str` has no
runtime representation yet.

[`crates/simple/examples/stdin.fn`](crates/simple/examples/stdin.fn) reads one
byte from standard input:

```text
main!(host) ->
  byte = host.read_byte!()
  host.exit!(add(byte 4))
```

`host.read_byte!()` returns `0` at EOF and `byte + 1` otherwise, so all 256
byte values remain distinct. The current one-result interface maps host read
errors to EOF. It is implemented by x86-64 Linux, wasm32 WASI, MOS 6502 sim65,
and the reference interpreter host contract. For ASCII `A`, this exits 70:

```sh
printf A | cargo run --bin faun-simple -- run crates/simple/examples/stdin.fn
printf 'status: %s\n' "$?"
```

This is byte input rather than a runtime string. Reading a whole stream still
needs a runtime sequence representation.


## Inspecting a runtime expression

[`crates/simple/examples/expressions.fn`](crates/simple/examples/expressions.fn) computes `(argc + 2) + argc`
with a guard requiring `argc < 32`. Counts include the program name: no extra
arguments gives exit status 4, two gives 8, and rejected counts give 0. Constant
arithmetic folds normally; the argument-dependent additions remain.

Enter the development shell, then inspect optimized Barb and lowered machine IR:

```sh
nix develop
cargo run --bin faun-simple -- inspect --target mos6502-sim65 --emit barb crates/simple/examples/expressions.fn
cargo run --bin faun-simple -- inspect --target mos6502-sim65 --emit ir crates/simple/examples/expressions.fn
```

Dumps go to stdout, so they can be redirected to files. `barb` stops after the
normal optimization schedule; look at `main!` for the folded constants 2 and 32.
It preserves source names such as `exit!` -- which is also the name every tier
below reads -- uses indentation for matches, and prints bodyless declarations
inline as `= <elsewhere>`.
`ir` is structurally validated machine IR, after its own optimization schedule
and before target preparation, useful even when a target cannot represent it. Use `--emit prepared-ir` for the legalized,
target-accepted IR that emission consumes. All stages honor the selected target's
host contracts and retain source validation and totality checks.

Build and run the 6502 image, then disassemble its actual emitted bytes:

```sh
cargo run --bin faun-simple -- build --target mos6502-sim65 -o /tmp/faun-expressions crates/simple/examples/expressions.fn
sim65 /tmp/faun-expressions.bin a b
echo $? # 8 (the result is an exit status, not printed output)

# Remove the 12-byte sim65 header; the payload loads at $0200.
dd if=/tmp/faun-expressions.bin of=/tmp/faun-expressions.raw bs=1 skip=12 status=none
da65 --cpu 6502 --start-addr 0x0200 /tmp/faun-expressions.raw
```

`sim65` and `da65` come with the development shell. Assembly is currently obtained
by disassembly, not a compiler `--emit asm` mode. This example has no embedded
data; programs with data or literal pools need a da65 info file to distinguish
those bytes from instructions.
