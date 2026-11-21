# barb

Barb is Faun's main IR: a small backend language with value semantics,
where the compiler selects every representation.

It sits where GHC's Core does, between the frontend and machine lowering,
but it is smaller: first-order, monomorphic and in A-normal form, with no
lambdas, type abstraction or laziness. There are five expression kinds.
Barb keeps the high-level shape of a program: types are still
constructors, loops are still recursion, a list is still a list. Because
the program says so little, there are few concepts to learn, and the
patterns worth optimizing are easy to find.

## Goals

- Competitive with LLVM with a fraction of the code
- Better code generation on tricky targets, such as the 6502
- Easy to add new backends

## Where Barb sits

The frontend supplies fully monomorphized, defunctionalized definitions.
Barb validates their structure, recognizes what they compute, derives facts
about them, and rewrites them while preserving value and effect semantics.
Its output is still Barb, which machine lowering consumes along with the
facts.

Place a proof or rewrite at the earliest tier that can express it
correctly:

- **Barb** owns list identities and fusion, recognized arithmetic, known
  values, sequence lengths and value ranges.
- **Machine IR** uses those facts to choose representations, storage
  placement, ownership operations and word widths. Barb's in-place pass
  expresses a walk as functional list replacements; machine lowering
  establishes when those replacements can reuse storage.
- **Target IR** selects instructions, addressing modes, registers and
  scheduling.

Machine recognizers remain useful fallbacks for hand-built IR and patterns
exposed by later passes. Target-dependent profitability and physical
storage choices stay below Barb.

## The IR

```
body ::= (x = expr)* expr         bindings, then the term that answers

expr ::= x                        a local, read back
       | Ctor(x*)                 a saturated construction
       | value                    known outright, held encoded
       | name(x*)                 a saturated call to a top-level name
       | match x { arm* }         an arm per constructor, in tag order

arm  ::= Ctor(x*) -> body         fields bound as the next locals

x    ::= a parameter, a binding, or a field an arm bound
```

## Semantics

What a Barb program means, and so what every pass keeps. A frontend may
rely on these; a pass that breaks one is wrong.

- **Values only.** A value is what it holds, never where: there is no
  identity, so a value may be copied, shared or rebuilt freely.
- **Representation is compiler-selected.** A frontend says what each type
  holds structurally. Barb classifies its shape and derives facts about its
  values. Machine lowering chooses its representation using those facts and
  the target's capabilities, and a program cannot observe which it chose.
- **Bodyless calls are observable.** Their order among themselves, how often
  each is made and on which paths are kept as written. A function whose
  calls reach one is observable too. There is no world value threaded
  through them: this rule is what orders them.
- **Pure work is only work.** A function reaching no bodyless call is pure.
  Its calls, and constructions, matches and recognized operations, may be
  left out where nothing reads them, moved to either side of an observable
  call, and moved onto only the paths that read them, even where they would
  not have come back: a hang that moves past an effect lets that effect
  happen first.
- **Optimization does less work, never more.** Each pass aims to do no more
  work on any path than its input did; inlining copies code, not
  evaluations. So an operand a function reads on only some paths tends to
  be worked out only on those once the function is inlined, which is how a
  frontend's lazily-read operators come out lazy without a rule of their
  own. That is the optimizer's doing, under its budgets, and not a promise:
  a frontend wanting it guaranteed emits the match itself.
- **What never comes back answers any type.** A call of a definition whose
  result type is uninhabited never answers, so it may answer an arm of any
  type: an arm the frontend knows no value takes. Machine lowering reads
  such a definition as one that never returns, and the joins after the arm
  take their width from the other arms alone.

## Input program requirements

Barb has value semantics. A bodyless call is a value the target computes.

- **Fully defunctionalized and monomorphized.**
- **Well-typed and exhaustive.** Validation checks structure, not types.
- **Functions with bodies need not stop.** A call whose answer is needed
  and never comes back hangs the program there. Pure work whose answer is
  not needed may be left out, so whether it would have stopped is not
  observable. Nothing is concluded from a call having answered.
- **Bodyless functions are implemented by the target**, and represent
  effects among other things. They are observable: optimization keeps their
  calls in order among themselves, made as often and on the same paths,
  with no world state threaded through them. A function whose calls reach
  one is observable too; one reaching none is pure.
  Pure work may move to either side of an observable call, and be left out
  where nothing reads it, even where it would not have come back: a hang
  that moves past an effect lets that effect happen first.
- **No identity or layout.** Because representation is selected for you,
  there is no pointer equality, reference identity or identity hashing; no
  sizeof, alignment, layout-dependent serialization or casts between
  representations; and no weak references or finalizers.
- **The whole program is available.** Dynamic linking of libraries may come
  later.
- **Exactly one entry.** Every program has one function a target enters,
  and validation refuses a program without it. Everything is rooted there:
  sweep keeps what the entry reaches, range analysis takes only the entry's
  parameters as coming from outside, and specialization never binds them.
  A library has no entry, so it never reaches Barb; the frontend's checks
  are all a library needs. Every defined function is still validated, so
  what is checked is everything written and what is kept is what runs.
- **Nothing to declare about floats or text.** A frontend that wants
  hardware floats uses the standard's float routines, which Barb knows by
  their code. Text and byte lists need no marking: a backend holds any
  sequence of byte-wide elements as bytes.

## Nothing is blessed, only recognized

Barb has no built-in integers, lists or strings. A number is recursion over
constructors, and `Bool` is a two-constructor type like any other. Barb
works out what a definition computes from its code, never from its name,
and records it as a fact.

A recognized definition keeps its body. The body is the meaning; the fact
lets passes fold a call and lets a target use one instruction for it. A
target without the instruction walks the body. A definition written some
other way is not recognized and runs as written: a miss costs speed, never
meaning.

### Recognized functions

Arithmetic on naturals, recognized from induction equations
(`Facts::operation`, an `Operation`). These are unbounded naturals, not
wrapping machine operations.

| `Operation`            | Computes                                    |
| ---------------------- | ------------------------------------------- |
| `Add`                  | `a + b`                                     |
| `Monus`                | `a - b`, or zero where `b` is larger        |
| `Mul`                  | `a * b`                                     |
| `Div`                  | `a / b`, or zero where `b` is zero          |
| `Mod`                  | `a % b`, or `a` where `b` is zero           |
| `And`, `Or`, `Xor`     | bitwise                                     |
| `Pow`                  | `a ^ b`, with `0 ^ 0` one                   |
| `Equals { yes, no }`   | `a == b`, answering one of two constructors |
| `LessThan { yes, no }` | `a < b`, answering one of two constructors  |

Sequences, recognized from the clauses that walk them
(`Facts::sequence_operation`, a `SequenceOperation`). Lowering answers each
from the buffer a sequence is held in rather than by walking it.

| `SequenceOperation` | Computes                                             |
| ------------------- | ---------------------------------------------------- |
| `Length`            | how many elements                                    |
| `ReverseOnto`       | the first's elements before the second's, last first |
| `Prepend`           | the first's elements before the second's, in order   |
| `Append`            | the first with one element after it                  |
| `Drop`              | the first without its first `n` elements             |
| `Take`              | the first `n` elements                               |
| `Replace`           | the first with element `n` replaced                  |

Floats, recognized by their code (`Facts::float`, a `Float` of an operation
and a format):

| Operation                          | Formats                |
| ---------------------------------- | ---------------------- |
| `Add`, `Sub`, `Mul`, `Div`, `Sqrt` | `Binary32`, `Binary64` |

No equation shows that a routine walking bits rounds as IEEE 754 does, so
Barb knows the standard's own float routines by fingerprint: a hash of a
definition's code and everything it calls, after canonicalizing, with no
name or ID in it. A definition whose fingerprint is in the table is that
routine. `just bless` writes the table from the standard, and the standard's
float expectations run both with the instructions and walking every body
(`Program::walk_floats`), which keeps it honest.

Barb also recognizes left rotations (`Facts::rotation`) and recursive tree
builders and readers (`Facts::tree_role`). Both are listed with the other
function facts below.

### Recognized data

`type_shape(program, ty)` classifies every type by its constructors alone.
Names and constructor order play no part. Machine IR picks a representation
from the shape, the facts below, and the target.

| `TypeShape`   | Constructors                    | Usually held as |
| ------------- | ------------------------------- | --------------- |
| `Uninhabited` | none                            | never built     |
| `Unit`        | one, no fields                  | nothing         |
| `Wrapper`     | one, one field                  | its field       |
| `Product`     | one, several fields             | fields, or cell |
| `Natural`     | empty; step of the rest         | word, or bignum |
| `Sequence`    | empty; step of element and rest | buffer          |
| `Spine`       | empty; step of fields and rest  | chain of cells  |
| `Enumeration` | several, no fields              | small tag       |
| `Sum`         | anything else                   | tagged cell     |

A sequence whose elements fit in a byte is held as bytes; text is a wrapper
around one. Nothing marks it.

## Facts

`program.analyze()` answers `Facts` about the program as it stands: a side
table indexed by function, expression, and constructor field. The program
itself stays plain Barb. A target with known guarantees asks
`program.assuming(&assumed)`, where `Assumed` says what entry parameters,
bodyless results and lengths can be, and whether floats are answered by
instructions; float facts appear only then.

Facts belong to one revision of the program. Function and expression IDs
can change when it is rewritten, so analyze after optimizing.

### Facts about functions

| Query                   | Answers                                            |
| ----------------------- | -------------------------------------------------- |
| `operation(f)`          | the arithmetic `f` computes, if recognized         |
| `sequence_operation(f)` | the sequence operation `f` computes, if recognized |
| `float(f)`              | the IEEE 754 operation `f` computes, if recognized |
| `rotation(f)`           | a recognized rotation and its width                |
| `tree_role(f)`          | whether `f` builds or reads a tree                 |
| `pure(f)`               | whether `f` has no effects                         |
| `answered(f)`           | whether calls of `f` are answered without its body |
| `takes(f)`              | the range of each parameter, over every call       |
| `answers(f)`            | the range of what `f` returns                      |

### Facts about values

| Query                 | Answers                                          |
| --------------------- | ------------------------------------------------ |
| `held(e)`             | range of the value `e` computes                  |
| `arguments(e)`        | range of each operand of call `e`, in its branch |
| `matched(e)`          | range of what match `e` takes apart              |
| `affine(e)`           | `e` as a constant plus locals times constants    |
| `float_comparison(e)` | `e` is the sign of a float difference            |

### Facts about data

| Query                    | Answers                                     |
| ------------------------ | ------------------------------------------- |
| `field(program, c, i)`   | range of field `i` of `c`, over every value |
| `type_shape(program, t)` | the shape of type `t`, above                |
| `unsettled()`            | a function whose ranges never settled       |

A range is a `Bounds`: a lowest value and, where one is known, a highest.
For a sequence it is a range of lengths. Ranges are what let machine IR hold
a number in a byte, a word, or a bignum, and know an index is in bounds
before anything asks.

An affine summary holds at most eight locals, each with a constant
coefficient. Where `unsettled()` names a function, range analysis gave up
and every bound is open.

## API

A frontend builds a `Program` and says nothing else about it:

1. Build types with `Program::declare_type` and `define_type`, and
   functions with `declare` and `define`. `Builder` constructs bodies in
   A-normal form.
2. `set_entry` names the entry, which every program has, and
   `answered_by` names the routine a bodyless declaration reaches.

Then:

3. `validate(&program)` checks structure and returns a `Refusal` on
   invalid input.
4. `optimize(&mut program)` runs the schedule below.
5. `program.analyze()` or `program.assuming(&assumed)` gives the `Facts`.
   The tier lowering for a target asks `program.for_target(&assumed,
   counted)` instead, for the program it lowers with its facts: where the
   target says how small a number it holds narrowly (`Counted`), each
   counted walk is split from a copy handed only numbers that small, a
   trade of work for time only the target can price.
6. `Program::render_analyzed` shows a program with its facts;
   `faun emit barb` prints it from the command line.

Barb is its own crate, `faun-barb`, read as `barb`, so what crosses the
boundary is exactly what is `pub` here. The frontend depends on it to build
a program; `faun-core`, the machine tier, depends on it to read one back
with its facts and to lower it. Barb depends on nothing else of the
compiler, and owns what the tiers below read in its words: `index`, the
pools and ranges every tier keeps a program in; `float`, the IEEE 754
operations it recognizes; and `Bounds`, what is known of a number, which
machine IR holds a value at. The `test-support` feature adds `fixture`, a small standard
library built with the builder, and `test_support`, the optimizer's single
steps and the `canonical` and `fingerprint` that write the float table from
the standard, for the tests of the tiers below; it also makes an ID from a
position, which a program alone does otherwise. Only dev-dependencies turn
it on.

## Optimization passes

`optimize` runs a fixed list of stages once, in this order, with no
switches. Each rewrites the program in place, and its output is plain
Barb.

1. **Canonicalization.** Tidy every body alone, recognize floats, then
   tidy again knowing what is recognized.
2. **Building forward.** A walk like `map` builds its list front to back,
   in tail calls.
3. **Descent.** A definition taking two numbers down together becomes its
   base cases on their differences.
4. **Constants.** A definition taking nothing that does work is folded
   where the budget allows, left to be inlined where it runs at most once,
   and otherwise worked out once in the entry and handed down as a
   parameter, so a walk naming it does not build it again every round.
5. **Inlining.** Copy helpers into callers, so mutual recursion becomes
   self-recursion.
6. **Fusion.** A list built by one walk and read once by another is never
   built.
7. **First element.** A list read only for its first element stops once it
   has it.
8. **In place.** A walk rebuilding a list element by element becomes
   indexed replacements.
9. **Simplification.** Callee-first constant folding, identities, and
   sharing repeated calls.
10. **Specialization.** Copy a loop for each known value its callers pass,
    where that decides a match.
11. **Joining rounds.** Inline again where specializing left two
    definitions calling each other.
12. **Sweep.** Drop what the entry doesn't reach.
13. **Cleanup.** Drop unused pure work, and move work into the one arm that
    reads it.

Pure work may be dropped or moved. Calls reaching a bodyless declaration
keep their order, count and path.

## Why this over LLVM

- LLVM makes a frontend choose a representation before it knows the
  target. Barb picks one per target, from facts about the values.
- Barb has no pointers, so it never needs alias analysis. Purity is a walk
  of the call graph, not a proof about memory.
- Barb has no undefined behavior. Every operation answers, hangs, or is an
  effect the target defines.
