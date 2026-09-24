# Barb

```
body = let x = expr ...; expr
expr = x
     | C(x...)
     | static k
     | f(x...)
     | match x { C(x...) => body, ... }
```

- First-order and A-normal.
- Locals are immutable de Bruijn levels.
- Calls and constructor applications are saturated.
- Arguments and match scrutinees are locals.
- Matches have exactly one arm per constructor.
- Constructor fields become the next locals in an arm.
- Functions may have a body or only a declaration.
- Declaration-only functions are interpreted by downstream consumers.
- Programs reaching this IR are well-typed, exhaustive, and total.
