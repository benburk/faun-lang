# Thoughts on effects

faun has a nice abstraction over host effects

```ruby
main! : Host -> []
main!(host) -> ...
```

- main!(host) is the root of all effects. environmental authority enters through host. there aren't any ambient globals. you have to pass host to call an effect
- `Host` is a nominal unforgeable type supplied by the target. No special notion of capabilities. its not an extra feature in the language. just possession of a nominal type with a private constructor
- Host can be subdivided into narrower components such as filesystem, network, stdin/stdout, GPU, GPIO, etc. This lets you give a library a subset of functionality e.g. only file I/O.
- Host startup data like `args`, `cwd` can simply be fields on the host record.
- Host APIs are defined by target, and statically structural. A program uses whatever host interfaces it requires, without naming or dispatching on the target
- If a target cannot provide an operation with the required semantics, it omits that operation. Compatibility checked at compile time
- Targets can expose extra functionality, e.g. NES hardware, or microcontroller GPIO. Programs using those interfaces can only compile on compatible targets
- Effectful host operations are explicit `!` calls. No host operation, cleanup callback, constructor/destructor, or other observable effect runs implicitly
- Host modules can define opaque resource types for identify bearing external state, e.g. files, sockets, OS handles, Vulkan buffers, command buffers, Metal objects, etc.
- Resources are unforgeable and linear. they cannot be copied or silently dropped. an effect can either borrow or consume them.
- Borrow is the cheap / default contract. Consumption is exceptional.
- Borrow/consume behavior is inferred, as Ori does, rather than written in signatures: a
  parameter only looked at on every path is lent, one used up or answered on every path is
  taken, and paths that disagree are refused (`crates/faun/src/linearity.rs`). The one
  written fact is the target's: a routine declared as using up its first argument
  (`fd_close!`) makes that argument's type a resource. It remains part of the API contract;
  an optional `consume` checked against the inferred contract is the way to make it visible.
- Resource mutation inside the host implementation is fine. `Buffer.write!`, `Socket.send!`, etc. mutate external state without introducing ordinary source-level mutable values.
- Explicit consuming operations handle cleanup: `close!`, `destroy!`, etc. No RAII/destructors/finalizers.
- The root as built:

  ```ruby
  main! : Host -> []
  exit! : (Host, U8) -> []
  ```

  `Host` is authority, not a resource: it is passed freely and never used up, and
  effects happen in the order they are written rather than by threading it. A status is a
  `U8`, since a byte is all of one every target keeps. Consuming `Host` at `exit!` was the
  earlier idea; linearity is kept for what a target says is used up, such as a `File`.

- Native libraries should be wrapped behind Faun-native host APIs rather than exposing arbitrary C declarations directly.
- Trusted target/native-extension implementations may call dylibs and deal with pointers, ABI layouts, callbacks, etc., but the API exposed to user code should only contain ordinary values, opaque types, resources, borrow/consume contracts, and explicit effects.
- This lets Metal, Vulkan, Win32, proprietary dylibs, etc. be supported without importing C's pointer/aliasing/lifetime model into user code.

Concrete host modules and their APIs are brainstormed in [effects/](effects/README.md).
