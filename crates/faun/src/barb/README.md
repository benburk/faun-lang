# barb

A simple compiler backend language with value semantics and automatic representation selection.

The idea is that, by encoding very little information in the program, there are fewer concepts to learn, and the compiler can derive the facts easily and optimize them.

## Goals

- Competitive with LLVM with a fraction of the code
- Better code gen on tricky targets, e.g. 6502
- Easy to add new backends

## Input program requirements

value semantics. a bodyless call is a value the target computes

- functions with bodies must be total - able to be proven to terminate by totality checker
- bodyless functions
  - can be used for representing effects
  - must be bodyless, implemented by the target
  - modeled by threading world state through calls
- must not have
  - pointer equality, reference identity, identity hashing. since representation is selected for you.
  - sizeof, alignment, layout dependent serialization, casts between representations
  - weak refs, finalizers
- whole source available. ish. backend will be able to dynamically link libs eventually
- must be fully defunctionalized and monomorphized

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

## Optimization passes

- A pass may not make a bodyless call run more times on any path than the program says.

## Why this over LLVM

- llvm makes you choose a representation before a target.
- barb doesn't have to prove expensive things like pointer aliasing, purity
- barb has no undefined behavior
