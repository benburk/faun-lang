# Modules

This note owns how a Faun program is divided into files and packages:
modules, `import` and `export`, the prelude every module sees, `package {}`
headers and their dependencies, and `expect`, the tests a module holds. What
a type's export hides of it is shared with [methods](methods.md) and
[tags](../values/tags.md).

## Modules and imports

Every file is a module. A module imports names from another by the other's
path, and names each one it takes. From the arena example's
`bots/random.fn`:

```ruby
export {RandomBot}

import pcg {Random}
import throw {Throw}
```

`import a.b {…}` finds `a/b.fn` or `a/b/b.fn`; where both exist, the import
is refused as ambiguous. A path is always read from the package's root, the
directory of its root module. So `bots/random.fn` imports `throw`, which
lies at the root, by the same spelling `main.fn` uses, and a module in
`sub/` imports its sibling as `sub.other`; a bare `other` is not found.

An import names what it takes. `{boxed: make}` binds `boxed` as `make`, and
`T.*` takes a type's constructors with it, as in
`import std.host {Host, Files, File, Mode.*}`. There is no wildcard: `{*}` does
not parse, and an import with no braces does not either. A name both
imported and declared in one module is refused, with the advice to import it
under another name.

The prelude, the standard library's exports, is seen by every module
without an import: `Bool`, `Nat`, `List`, `Str`, `Map` and the rest. A
module may not declare a type the prelude has. The standard library's own
modules are not imported by name; `std.host`, the target's host module, is
the one standard module a program imports.

Imports form no cycle. A module importing one that imports it back, directly
or through others, is refused: "import cycle through …".

## Exports

A module exports nothing it does not list. `export {…}` names what other
modules may import, as the arena's `arena.fn` does:

```ruby
export {Player, Tally, Score, play, pairs, tournament}
```

Importing anything else is refused: "`one` is not exported by `helper`".
A type exported as `T` takes its methods with it and keeps its constructors
private. Exported as `T.*`, its constructors are public, and an importer
may take one alone, `import std.host {Read}`. A private constructor cannot
be reached by qualifying it, `Failure.NotFound`, and a structural tag of the
same spelling is not one, so another module cannot forge the type's values.
An alias owns no constructors, so `export {Numbers.*}` of an alias is
refused, and a name the module cannot see cannot be exported.

A module may export what it imported. The standard library's root does
nothing else: it imports `bool {Bool.*}` and its siblings, and its export
list is the prelude.

## Packages

A package is its root module's directory and every module it imports from
there. Its root may name the packages it depends on in a header, each by a
module base relative to the header's file:

```ruby
package {
  md5: "../libraries/md5/src/md5"
}

import md5 {md5_hash}
```

That is `examples/aoc/201504.fn`. The name on the left is the depending
package's choice: the arena calls the random-number library `pcg`. Any
module of the package may then import that name, which is the dependency's
root module.

- A dependency's inner modules are its own: `import shapes.area {square}`
  is refused, saying to import `shapes` itself.
- A dependency's modules resolve their imports from its own root, with its
  own header's dependencies, wherever it sits on disk.
- Only a package's root module has a header; one in an inner module is
  refused, and so is a name depended on twice.
- A dependency is a path that must name a module: there is no fetching, no
  version and no lock file. A URL is refused as one: a dependency is a path to a package's root module.

Whether a package is an application is whether its entry defines `main!`.

## Expectations

`expect` followed by a `Bool` expression or a block is a claim a module
makes of its own definitions:

```ruby
double : Nat -> Nat
double(n) -> n * 2

expect double(2) == 4
expect (
  doubled = [1, 2, 3].map(double)
  doubled.len() == 3
    & doubled.last().ok_or(0) == 6
)
```

An expectation is checked as a definition is, whenever its package is
checked: `expect 3` is a type error under `faun check`. It may use the
module's private definitions. No program can name one, and it reaches no
host, so it is pure.

`faun test PATH` builds the package at `PATH` with an entry of its own in
place of any `main!`, asks every expectation of every module in the
package, and prints the number that do not hold and where each was
written. The expectations of the packages it depends on, the standard
library's among them, are theirs to test: a package is tested by running
`faun test` on it.

## Rationale

### Why are imports absolute?

So a module has one name everywhere in its package. With imports relative
to the importing file, `main.fn` and `bots/random.fn` would name `throw`
differently, and moving a file would change the imports inside it. Read
from the root, moving a file changes only the imports that name it. The
cost is spelling the full path from the root, `sub.other`, even for a
sibling.

### Why no wildcard imports?

Every name a module uses is declared in it, named in one of its imports, or
the prelude's, so where a name comes from is found at the top of the file.
And since a name both imported and declared is refused, a wildcard would
let a dependency break its importers by exporting something new whose name
an importer already declares. Naming each import costs a longer line;
`{boxed: make}` renames where two names would meet.

### Why must a module list its exports?

So that adding a definition never widens what other modules can depend on.
A helper is private until the export list says otherwise, and the list,
read in one line, is the module's whole interface. A type's constructors
are a second decision, `T` or `T.*`, because exposing a representation is
not the same as exposing a type: `Str` is exported with its methods and
without its wrapper, so other modules make text only through literals and
`Str`'s own methods, such as `from_utf8`. The cost is keeping the list in
step with the module, and writing a method for anything a caller needs
that a hidden constructor would have given it.

### Why no import cycles?

Each module is loaded after the modules it imports, so its imports'
interfaces are complete when its own names are resolved, and a program's
modules form layers that can be read from the bottom up. The recourse for
two modules that need each other is a third holding what they share. The
cost falls on types that refer to each other: they live in one module.
The standard library's types are one such vocabulary across files, `Bool`
answering `Str` and `Str` measured in `Nat`, and that works because every
module sees the prelude rather than importing it.

### Why `package {}` headers with path dependencies?

A package should mean the same wherever it sits. Its root's header holds
its whole dependency map, its imports are read from its own root, and its
inner modules are hidden from whoever depends on it, so a library can be
copied beside a program, or under it, without a line inside it changing.
The depending package names each dependency, so two libraries with one
name, or a library under a shorter name, need no change to either.

Dependencies are local paths because fetching, hashing, locking and
choosing versions are a package manager's work, and there is none. The
cost is that a path's surroundings are part of the package: moving a
library moves the paths of everything that depends on it.

### Why are tests `expect`s in the module?

A test beside what it tests is read with it, kept in step with it, and
sees its private definitions, so nothing is exported only to be tested.
Since an expectation is a definition, a test that no longer type-checks is
an error under `faun check`, not a failure found later. And a test is only
a `Bool`, so no test framework, assertion library or runner protocol is
needed; the standard library holds 83 expectations and the examples about
780. What the compiler can settle while compiling it settles there, before
the program runs.

The cost: a failing expectation says where it is, not which values made it
fail, and an expectation is pure, so a test of effects is a program of its
own. Property tests are a library, `examples/libraries/proptest`, whose
`forall` takes a generator, a property and a shrinker as callbacks.

## Related

- [Methods](methods.md): what exporting a type exports of it
- [Tags](../values/tags.md): constructors, structural tags, and why a tag
  cannot forge a sealed type
- [Effects](effects.md): `std.host`, `main!` and the capabilities a program
  is handed
- [Functions](../values/functions.md): `expect` bodies are clauses of no
  parameters, as values are
- [Computation](../computation.md): what the compiler may settle before a
  program runs
