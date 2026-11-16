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
module may not declare a type the prelude has, so a name added to the
prelude is one a [language version](#header-fields-not-built) admits. The
standard library's own modules are not imported by name; `std.host`, the
target's host module, is the one standard module a program imports.

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
there. Its root may begin with a header, a record of fields, each optional:

```ruby
package {
  faun: "0.1",
  uses: {
    md5: "../libraries/md5/src/md5",
  },
  test_uses: {
    proptest: "../libraries/proptest/src/proptest",
  },
}

import md5 {md5_hash}
```

- `uses` names the packages it depends on, each by a module base relative
  to the header's file.
- `test_uses` names those only its expectations need, in the same way.
- `faun` is the language version it is written for, `MAJOR.MINOR`.

A field the header does not have, one written twice, or one holding the
wrong kind of value is refused. A file needs no header at all: a script
with no dependencies is a file and nothing more.

The name on the left of a dependency is the depending package's choice: the
arena calls the random-number library `pcg`. Any module of the package may
then import that name, which is the dependency's root module.

- A dependency's inner modules are its own: `import shapes.area {square}`
  is refused, saying to import `shapes` itself.
- A dependency's modules resolve their imports from its own root, with its
  own header's dependencies, wherever it sits on disk.
- Only a package's root module has a header; one in an inner module is
  refused, and so is a name depended on twice, in one field or across
  `uses` and `test_uses`.
- A dependency is a path that must name a module, or a
  [URL](#url-dependencies) that names a bundle.

Whether a package is an application is whether its entry defines `main!`.

### Language versions

`faun` is read the way Rust reads an edition and Go its `go` line: each
package is read by its own version's rules, so one build mixes packages
written for different versions. A version newer than the compiler's own,
the major and minor of its release, is refused, saying so.

A header without `faun` is read by the running compiler's own version, so
a script or a project of one's own always has the current language and is
fixed by hand when the language changes. A language change that would
break a package, a name added to the prelude among them, applies only to
packages whose version is new enough. No change has needed one yet, so
today every version up to the compiler's is read alike.

The version is a request to whichever compiler runs, not a pin of one:
fetching and running a compiler is left to the tools that install it, a
Nix flake among them.

### Test dependencies

A package's test code is its expectations and what only they reach, a
helper they share included. Its real code is the rest: what its root
exports and its `main!` reach, and any definition nothing reaches. Real
code that names something only a `test_uses` package gives is refused, at
that name, with the chain real code reaches it by, and the advice to move
the dependency to `uses`:

```text
error: `double_square` is from a test dependency, and real code uses it
  --> main.fn:13:14
   |
13 | scaled(n) -> double_square(n)
   |              ^^^^^^^^^^^^^ `scaled` uses it
   |
   = note: only expectations, and what only they reach, may use a package in `test_uses`
   = note: real code reaches it: `area` calls `scaled`
```

A definition reaches the globals, constructors and types it names, and,
since a method is found by its receiver's type, every method of the
package spelled as a member it asks for.

A dependency's own `test_uses` that are URLs are fetched as written and
take no part in choosing versions, so its test tooling never changes what
the packages depending on it build with.

Planned, not built: a `uses` dependency only test code reaches gets a
warning suggesting `test_uses`, and a package checked as another's
dependency has its expectations left unchecked, so its `test_uses`
packages are not fetched at all.

### URL dependencies

This follows Roc's packages. A dependency may be an `https` URL to a
bundle, a `.tar.zst` file named by the BLAKE3 hash of its bytes:

```ruby
package {
  uses: {
    pcg: "https://example.com/pcg/1.2.0/4ZuGvfzgQ8bm8nVz7dLNYRTYHoNeuDLPdrvzeAUm7gwF.tar.zst",
    md5: "../libraries/md5/src/md5",
  },
}
```

- The URL's last segment, before `.tar.zst`, is the hash in base58. A URL
  without one is refused. After downloading, the compiler hashes the bytes
  it read and refuses the bundle if they differ, so a URL always names the
  same contents, whatever the server does later. A URL with a query or a
  fragment is refused.
- `faun bundle PATH` makes the bundle of the package at `PATH`: its root
  module, as `main.fn` at the bundle's top, and every module it imports, at
  their paths from the root, with the compiler's language version written
  into the root's header where it has none. Every entry is written alike,
  owned by no one and dated to the epoch, so bundling a package twice
  writes the same bytes. It writes the file under its hash, `-o DIR` saying
  where, to be uploaded anywhere that serves static files over `https`. The
  bundle is what is hashed, so what a dependency names is the file its
  author made, never an archive a forge generates. A package depending on
  another by a path is refused, since the bundle cannot hold it: each is
  bundled, and named by its URL.
- Plain `http` is allowed only to `localhost`, for testing. A redirect is
  followed at most three times, and each place it leads must keep the same
  rule.
- A bundle may unpack to at most 10 megabytes, and everything one command
  fetches to at most 100, and holds only files and directories, each inside
  it. A flag to raise the limits is planned.
- A fetched package is kept in the user's cache, `$XDG_CACHE_HOME/faun/`
  (`~/.cache/faun/` when that is unset, and `$FAUN_CACHE` where that is
  set), under `packages/` and its hash, read-only and
  shared by every project on the computer. A bundle is unpacked into a
  staging directory and moved into place with a rename, so a directory
  named by a hash always holds a whole package; a staging directory a day
  old is left from a killed process and is removed. A build whose packages
  are all cached reaches no network.
- A fetched package is a package like any other: its imports read from its
  own root, its inner modules are its own, and its own header names its own
  dependencies, which may be paths within it or URLs.
- The `faun` command fetches what a package needs before it checks, builds,
  runs or tests it. The compiler itself only reads the cache: fetching is
  the command's.

#### Versions

A URL may hold one version, `MAJOR.MINOR.PATCH`, anywhere before the hash,
as `1.2.0` above. More than one is refused. Two URLs that differ only in
their version and hash are versions of one package, and where a build's
packages depend on one package more than once, versions choose which copy
is used:

- Versions with different majors, `1.4.0` and `2.0.0`, are different
  packages, and both are used.
- Versions with one major, `2.1.0` and `2.3.1`, are compatible, and the
  build uses the highest the dependency graph mentions, everywhere.
- Below `1.0.0` the minor is the major: `0.3.0` and `0.4.0` are different,
  and `0.3.0` and `0.3.5` compatible.
- The package being built uses its own dependencies as written. A higher
  version wanted deeper in the graph is refused, showing the chain of
  dependencies that wants it, rather than upgraded silently.
- A URL with no version is its own package, never merged with another.

Choosing is a fixed point, not a search: follow only the chosen versions'
dependencies, take each group's highest mentioned version, and repeat
until nothing changes. A version mentioned only by a package that was not
chosen no longer counts. There is no lock file, because the headers and
this rule decide every package a build reads.

Two packages that are used side by side, two majors of one library or two
URLs without versions, have two sets of types: a `Random` from one is not a
`Random` from the other, and passing one where the other is wanted is a
type error.

#### Commands

- `faun fetch PATH` downloads every dependency of the package at `PATH`, so
  a later build can be offline.
- `faun uses PATH` prints the dependency graph as a tree, each dependency
  by the URL or path its header wrote, marking a package shown before, a
  test dependency, and a version chosen in place of the one written.
- Planned, not built: `faun bump PATH` compares a package's exported
  interface with its previous version's and says whether the change is
  major, minor or patch.

Vendoring a dependency is unpacking its bundle beside the package and
writing its path in place of the URL. A path dependency is read as it is,
never fetched, cached or versioned.

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

A path dependency is read as it is, with nothing fetched, hashed or
chosen. The cost is that a path's surroundings are part of the package:
moving a library moves the paths of everything that depends on it, which
is what a URL dependency is for.

### Why URLs named by hash, and Roc's versions?

A path dependency means the same wherever its package is copied, but only
on a computer that has the library at that path. A URL named by a hash
keeps the promise everywhere: the header names exact bytes, the cache holds
them by that name, and whatever server answers, what is read is what the
hash says. Roc has shipped this design, and following it borrows the
answers to questions a first design gets wrong: which bytes to hash, how a
shared cache survives two builds at once, how big a download may be, and
where a redirect may lead.

The bundle is made by `faun bundle`, not by a forge, because archives a
forge generates are not stable bytes: GitHub's changed compression in 2023
and broke every pinned hash of them. Hashing a file its author uploaded
makes hashing the bytes enough, and the hash is checked as the download
streams in. Faun's bundle needs no list of files, since a package is its
root and what that imports.

A lock file is needed where a manifest asks for a range, `^1.2`, and a
resolver searches for one version that satisfies every range, a problem
that is NP-complete in general and a SAT solver in practice. A URL names
one version, so there is nothing to search: the highest mentioned in each
compatible group is a rule anyone can apply by hand, and Go's minimal
version selection showed that such a rule is enough. Merging compatible
versions is what keeps one library's types one set of types across a
program; keeping every version apart would build both, with types that
cannot meet.

The cost is that versions are read by the compiler, not only by people,
and a library that breaks its interface in a minor release breaks the
packages that depend on it. `faun bump`, when it is built, is the check
against that.
Upgrading stays an edit to a header, which a tool can make by reading a
library's releases; the compiler never chooses a version newer than one
some header wrote.

Fetching runs nothing. A Faun package has no build script, so fetching one
is reading bytes, and a hash that matches says only that they are the bytes
the header's author chose, not that they are safe.

### Why a header of fields, with a language version?

A bundle never changes, so every header ever bundled must be read by every
later compiler: the header's shape is the one thing that cannot be changed
later. A record of named fields leaves room, and a field added later is
one a language version admits. The fields are few because Faun has no
registry and no build steps: a package's name is its importer's choice, its
version is in the URL, and what Cargo's features, profiles and build
scripts do is not Faun's to do.

The language version is what lets a frozen package outlive the language
changing under it. Without one, a name added to the prelude breaks every
package that declares its own, bundles nobody can edit among them, and an
old package on a new compiler fails with an error from deep inside it
rather than one saying which version it was written for. A missing version
means the running one, unlike Rust, where a missing edition is the oldest,
so a script never needs a header; `faun bundle` writing it is what keeps
the bundles, the only packages that cannot be fixed, from going without.
The cost is that every rule a version changes stays in the compiler for
the packages written before it.

`test_uses` is listed rather than inferred from what test code reaches,
though the compiler computes the same thing either way. Inferred, a test
helper called once from real code would become a dependency of every
package depending on this one, and with the highest mentioned version
chosen, its version mentions would change their builds, with nothing
saying so. Listed, that is a refusal, and changing what a package asks of
the packages depending on it is always an edit to its header.

Overriding a dependency deep in the graph, Cargo's `[patch]` or Go's
`replace`, is left out, both as a field and as a flag for one command. A
newer version is taken by mentioning it, since the highest mentioned is
used, and a fork is a vendored copy, with the packages between it and the
root vendored too. An override can come when a case needs it.

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
