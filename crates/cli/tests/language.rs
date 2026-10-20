//! The language as Ori defines it, case by case: what a program answers.
//! Why one is refused is in `refused/`, beside the program.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
    (
        "a numeral an expression's arms test is tested as a clause's is",
        "bucket : Nat -> Nat
         bucket(x) -> x is (
           70 then 1
           200 then 2
           _ then 0
         )
         
         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(bucket(n + 69) * 10 + bucket(n + 199) + bucket(n)))
         )",
        12,
    ),
    (
        "numerals past what is taken apart beside a successor are each tested once",
        "f : Nat -> Nat
         f(0) -> 3
         f(2000) -> 1
         f(70) -> 5
         f(Succ(n)) -> if n > 100 then 7 else n % 50
         
         main! : Host -> []
         main!(host) -> (
           k = host.args.len()
           host.exit!(U8.of_nat(f(k - 1) + f(k + 1999) * 10 + f(k + 69) * 20 + f(k + 9) + f(k + 300)))
         )",
        129,
    ),
    (
        "a bound asking its own method again at the same types is met where it is asked",
        "Box(a) : [B(a)].(
           foo : (Box(a), b) -> Nat where b.foo : (b, b) -> Nat
           foo(_, _) -> 6
         )
         
         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(B(1).foo(B(2))))",
        6,
    ),
    (
        "a record holding itself through another record is held whole there",
        "import std.host {Host, File}
         
         Wrap(a) : {x: a}
         Node : {file: File, next: Wrap(Node)}
         
         count : Node -> Nat
         count(_) -> 0
         
         main! : Host -> []
         main!(host) -> host.exit!(9)",
        9,
    ),
    (
        "clauses ending a list in fewer elements each try the next once, not once for each way the last fails",
        "f : List(Nat) -> Nat
         f([*_, a0, a1, a2, a3, a4, a5, a6, a7]) -> 8 * 10 + a0
         f([*_, a0, a1, a2, a3, a4, a5, a6]) -> 7 * 10 + a0
         f([*_, a0, a1, a2, a3, a4, a5]) -> 6 * 10 + a0
         f([*_, a0, a1, a2, a3, a4]) -> 5 * 10 + a0
         f([*_, a0, a1, a2, a3]) -> 4 * 10 + a0
         f([*_, a0, a1, a2]) -> 3 * 10 + a0
         f([*_, a0, a1]) -> 2 * 10 + a0
         f([*_, a0]) -> 1 * 10 + a0
         f([]) -> 0
         
         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(f([n, 2, 3]) + f([n]) + f([]) + f([n, 1, 1, 1, 1, 1, 1, 1, 1, 1])))
         )",
        123,
    ),
    (
        "guarded clauses each fall through to the next once, not once for each way the guard fails",
        "Opt : [Some(Nat), None]
         
         g : Opt -> Nat
         g(x) if x is Some(y) & y == 0 -> 0
         g(x) if x is Some(y) & y == 1 -> 1
         g(x) if x is Some(y) & y == 2 -> 2
         g(x) if x is Some(y) & y == 3 -> 3
         g(x) if x is Some(y) & y == 4 -> 4
         g(x) if x is Some(y) & y == 5 -> 5
         g(x) if x is Some(y) & y == 6 -> 6
         g(x) if x is Some(y) & y == 7 -> 7
         g(x) if x is Some(y) & y == 8 -> 8
         g(x) if x is Some(y) & y == 9 -> 9
         g(x) if x is Some(y) & y == 10 -> 10
         g(x) if x is Some(y) & y == 11 -> 11
         g(x) if x is Some(y) & y == 12 -> 12
         g(x) if x is Some(y) & y == 13 -> 13
         g(x) if x is Some(y) & y == 14 -> 14
         g(x) if x is Some(y) & y == 15 -> 15
         g(x) if x is Some(y) & y == 16 -> 16
         g(x) if x is Some(y) & y == 17 -> 17
         g(_) -> 50
         
         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(g(Some(n + 4)) + g(Some(n + 40)) + g(None)))
         )",
        105,
    ),
    (
        "a guard of alternatives each testing goes on to the next clause once",
        "h : (Bool, Bool) -> Nat
         h(a, b) if (a is True | b is True) & (a is True | b is True) & (a is True | b is True) & (a is True | b is True) & (a is True | b is True) & (a is True | b is True) -> 7
         h(_, _) -> 3
         
         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(h(n == 1, False) * 10 + h(False, n == 2)))
         )",
        73,
    ),
    (
        "a chain of else ifs each testing is written once, not once for each part of the tests before",
        "Opt : [Some(Nat), None]
         
         pick : Opt -> Nat
         pick(o) -> (
           if o is Some(y) & y == 0 then 100
           else if o is Some(y) & y == 1 then 1
           else if o is Some(y) & y == 2 then 2
           else if o is Some(y) & y == 3 then 3
           else if o is Some(y) & y == 4 then 4
           else if o is Some(y) & y == 5 then 5
           else if o is Some(y) & y == 6 then 6
           else if o is Some(y) & y == 7 then 7
           else if o is Some(y) & y == 8 then 8
           else if o is Some(y) & y == 9 then 9
           else if o is Some(y) & y == 10 then 10
           else if o is Some(y) & y == 11 then 11
           else if o is Some(y) & y == 12 then 12
           else if o is Some(y) & y == 13 then 13
           else if o is Some(y) & y == 14 then 14
           else if o is Some(y) & y == 15 then 15
           else if o is Some(y) & y == 16 then 16
           else if o is Some(y) & y == 17 then 17
           else if o is Some(y) & y == 18 then 18
           else if o is Some(y) & y == 19 then 19
           else if o is Some(y) & y == 20 then 20
           else if o is Some(y) & y == 21 then 21
           else 50
         )
         
         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(pick(Some(n + 6)) + pick(Some(n + 60)) + pick(None)))
         )",
        107,
    ),
    (
        "loops nested deep are each read ahead once",
        "count : Nat -> Nat
         count(z) -> (
           t = z
           while t < 1 do (
             while t < 1 do (
               while t < 1 do (
                 while t < 1 do (
                   while t < 1 do (
                     while t < 1 do (
                       while t < 1 do (
                         while t < 1 do (
                           while t < 1 do (
                             while t < 1 do (
                               while t < 1 do (
                                 while t < 1 do (
                                   while t < 1 do (
                                     while t < 1 do (
                                       while t < 1 do (
                                         while t < 1 do (
                                           while t < 1 do (
                                             while t < 1 do (
                                               while t < 1 do (
                                                 while t < 1 do (
                                                   while t < 1 do (
                                                     while t < 1 do (
                                                       while t < 1 do (
                                                         while t < 1 do (
                                                           t = t + 1
                                                         )
                                                       )
                                                     )
                                                   )
                                                 )
                                               )
                                             )
                                           )
                                         )
                                       )
                                     )
                                   )
                                 )
                               )
                             )
                           )
                         )
                       )
                     )
                   )
                 )
               )
             )
           )
           t
         )
         
         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(count(host.args.len() - 1) + 40))",
        41,
    ),
    (
        "a buffer handed through many ifs in a round is asked about once for each",
        "work : (List(U8), Nat) -> Nat
         work(xs, n) -> (
           i = 0
           count = 0
           while i < n do (
             xs = xs.set(i % 3, U8.of_nat(i % 200)).ok_or([])
             (xs, count) = if i % 2 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 3 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 4 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 5 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 6 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 7 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 8 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 9 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 10 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 11 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 12 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 13 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 14 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 15 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 16 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 17 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 18 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 19 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 20 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 21 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 22 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 23 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 24 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 25 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 26 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 27 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 28 == 0 then (xs, count + 1) else (xs, count)
             (xs, count) = if i % 29 == 0 then (xs, count + 1) else (xs, count)
             i = i + 1
           )
           xs.len() + count
         )
         
         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(work([1, 2, 3], host.args.len())))",
        31,
    ),
    (
        "a walk building a list whose base case answers something else of it compiles",
        "w : (List(Nat), List(Nat)) -> Nat
         w(xs, built) -> xs is (
           [] then built.len()
           [x, *rest] then w(rest, built.append(x + 1))
         )

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(w([1, 2, 3].take(host.args.len() + 1), [])))",
        2,
    ),
    (
        "a helper doubling what it is handed is no larger for arithmetic recognition to read",
        "d : Nat -> Nat
         d(n) -> (
           m = n + n
           p = m + m
           q = p + p
           if q > 1000000 then q else d(q)
         )

         w : (Nat, Nat) -> Nat
         w(a, _) -> d(a + 1)

         main! : Host -> []
         main!(host) -> (
           k = host.args.len()
           host.exit!(U8.of_nat(w(k, k) / 65536))
         )",
        64,
    ),
    (
        "a recursive call at another type that stops growing needs finitely many definitions",
        "size : (a, Nat) -> Nat
         size(_, 0) -> 0
         size(_, n) -> 1 + size(n, n - 1)

         Tree(a) : [Leaf(a), Node(List(Tree(a)))]

         leaves : Tree(a) -> Nat
         leaves(Leaf(_)) -> 1
         leaves(Node(children)) -> children.fold(0, |sum, child| sum + leaves(child))

         main! : Host -> []
         main!(host) -> (
           tree = Node([Leaf(\"a\"), Node([Leaf(\"b\"), Leaf(\"c\")])])
           host.exit!(U8.of_nat(size(\"s\", 3) * 10 + leaves(tree)))
         )",
        33,
    ),
    (
        "an order chained with `|` works out the next only where the first ties",
        "forever : Nat -> Nat
         forever(n) -> forever(n + 1)

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           order = n.cmp(n + 1) | forever(n).cmp(0)
           host.exit!(if order.lt() then 7 else 0)
         )",
        7,
    ),
    (
        "a list of words mapped, written without asking, is read after as it was",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           xs = [U32.of_nat(n), U32.of_nat(n + 1), U32.of_nat(n + 2)]
           ys = xs.map(|x| x + 10)
           host.exit!(U8.of_nat(xs.fold(0, |s, x| s + x.to_nat()) * 10 + ys.fold(0, |s, y| s + y.to_nat()) + ys.len() - 3))
         )",
        96,
    ),
    (
        "a list a walk rewrites through another walk is read after as it was",
        "pass : List(Nat) -> List(Nat)
         pass([x, *rest]) -> (
           (total, others) = rest.map_accum(x, |s, y| (s + y, y + 1))
           [total, *pass(others)]
         )
         pass([]) -> []

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           xs = [n, n + 1, n + 2]
           ys = pass(xs)
           host.exit!(U8.of_nat(xs.fold(0, |s, x| s * 10 + x) - 100 + ys.fold(0, |s, y| s + y) + ys.len() - 3))
         )",
        41,
    ),
    (
        "a walk going on with what it worked out is fused with the map after it",
        "pass : List(Nat) -> List(Nat)
         pass([x, *rest]) -> (
           (total, others) = rest.map_accum(x, |s, y| (s + y, y + 1))
           [total, *pass(others)]
         )
         pass([]) -> []

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           ys = pass([n, n + 1, n + 2]).map(|y| y * 2)
           host.exit!(U8.of_nat(ys.fold(0, |s, y| s + y) + ys.len() - 3))
         )",
        36,
    ),
    (
        "a list mapped is read after as it was",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           xs = [n, n + 1, n + 2]
           ys = xs.map(|x| x + 10)
           host.exit!(U8.of_nat(xs.fold(0, |s, x| s + x) * 10 + ys.fold(0, |s, y| s + y) + ys.len() - 3))
         )",
        96,
    ),
    (
        "a list nothing else holds is mapped where it lies",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           ys = [n, n + 1, n + 2].map(|x| x * 2)
           host.exit!(U8.of_nat(ys.fold(0, |s, y| s * 10 + y) + ys.len() - 3))
         )",
        246,
    ),
    (
        "a list mapped with a running state keeps the state and the order",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           (total, ys) = [n, n + 1, n + 2].map_accum(0, |s, x| (s + x, s))
           host.exit!(U8.of_nat(total * 10 + ys.fold(0, |s, y| s * 10 + y)))
         )",
        73,
    ),
    (
        "a definition that never stops for some inputs is a program all the same",
        "step : Nat -> Nat
         step(Succ(n)) -> hop(n)
         step(Zero) -> 7

         hop : Nat -> Nat
         hop(m) -> step(Succ(Succ(m)))

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(step(0)))",
        7,
    ),
    (
        "a large numeral is a test, however large",
        "code : Nat -> Nat
         code(13) -> 1
         code(95) -> 2
         code(2000) -> 3
         code(_) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(95) * 27 + code(2000) * 9 + code(13) * 3 + code(7)))",
        84,
    ),
    (
        "a large signed numeral is a sign and a test",
        "sign : Int -> Nat
         sign(-40) -> 5
         sign(40) -> 6
         sign(_) -> 7

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(sign(-40) * 25 + sign(40) * 5 + sign(-39)))",
        162,
    ),
    (
        "a type nothing pins is Nat",
        "main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat([].len() + [[], []].len()))",
        2,
    ),
    (
        "a function, a constructor and a lambda are passed into calls",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         main! : Host -> []
         main!(host) -> (
           doubled = [1, 2].map(twice).fold(0, |s, x| s + x)
           wrapped = [3].map(Ok).map(|r| r.ok_or(0)).fold(0, |s, x| s + x)
           host.exit!(U8.of_nat(doubled + wrapped))
         )",
        9,
    ),
    (
        "an alias is its type",
        "MyError = [NotFound, SomethingElse]
         Point = {x: Nat, y: Nat}
         Numbers = List(Nat)

         cat : Nat -> Result(Nat, MyError)
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         sum : Point -> Nat
         sum({x, y}) -> x + y

         total : Numbers -> Nat
         total(xs) -> xs.fold(0, |s, x| s + x)

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(cat(5).ok_or(0) + sum({x: 1, y: 2}) + total([4])))",
        12,
    ),
    (
        "an alias with parameters is its type at each use's arguments",
        "Edge(e) = {target: Nat, weight: e}
         Pair(a, b) = (a, b)
         Weighted(e) = List(Edge(e))

         heaviest : Weighted(Nat) -> Nat
         heaviest(edges) -> edges.map(|edge| edge.weight).max().ok_or(0)

         targets : Weighted(e) -> List(Nat)
         targets(edges) -> edges.map(|edge| edge.target)

         swap : Pair(a, b) -> Pair(b, a)
         swap((x, y)) -> (y, x)

         main! : Host -> []
         main!(host) -> (
           edges = [{target: 4, weight: 30}, {target: 2, weight: 7}]
           (named, _) = swap((1, \"a\"))
           labelled = [{target: 3, weight: \"x\"}]
           host.exit!(U8.of_nat(heaviest(edges) + targets(labelled).sum() + named.len()))
         )",
        34,
    ),
    (
        "the ordering operators are views of one cmp",
        "bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) -> (
           n = host.args.len() + 2
           a = bit(n < 5) + bit(n <= 3) * 2 + bit(n > 3) * 4 + bit(n >= 3) * 8
           b = bit(-2 < 1) * 16 + bit(-3 < -2) * 32 + bit(False < True) * 64 + bit(2 > 7) * 128
           host.exit!(U8.of_nat(a + b))
         )",
        123,
    ),
    (
        "a type is ordered by defining cmp",
        "Size : [Small, Large].(
           cmp : (Size, Size) -> Order
           cmp(Small, Large) -> Lt
           cmp(Large, Small) -> Gt
           cmp(_, _) -> Eq
         )

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat((Small < Large).to_nat() + (Large <= Small).to_nat() * 2))",
        1,
    ),
    (
        "? answers an Err early and joins its producers' rows",
        "cat : Nat -> Result(Nat, [NotFound, SomethingElse])
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         dog : Nat -> Result(Nat, [Blah, NotFound])
         dog(0) -> Err(NotFound)
         dog(1) -> Err(Blah)
         dog(n) -> Ok(n)

         foo : Nat -> Result(Nat, [Blah, NotFound, SomethingElse])
         foo(n) -> (
           x = cat(n)?
           y = dog(n + 1)?
           Ok(x + y)
         )

         inline(n) -> Ok(cat(n)? + dog(n)? * 2)

         code : Result(Nat, [Blah, NotFound, SomethingElse]) -> Nat
         code(Ok(n)) -> n
         code(Err(NotFound)) -> 100
         code(Err(SomethingElse)) -> 101
         code(Err(Blah)) -> 102

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(foo(5)) + code(foo(1)) + code(foo(0)) + code(inline(3)) - 190))",
        31,
    ),
    (
        "? in a lambda answers from the lambda",
        "half : Nat -> Result(Nat, [Odd])
         half(n) if n % 2 == 0 -> Ok(n / 2)
         half(_) -> Err(Odd)

         main! : Host -> []
         main!(host) -> (
           halves = [2, 4].map(|n| Ok(half(n)? + 1))
           host.exit!(U8.of_nat(halves.map(|r| r.ok_or(0)).fold(0, |s, x| s + x)))
         )",
        5,
    ),
    (
        "tuples, record rows, updates and destructuring",
        "swap : ((Nat, Bool)) -> (Bool, Nat)
         swap((n, b)) -> (b, n)

         first((k, _)) -> k

         get_name : {name: Nat, *} -> Nat
         get_name(r) -> r.name

         age_of(r) -> r.age

         older(r) -> {age: r.age + 1, *r}

         sub(x, y) -> subtract((x, y))
         subtract((0, _)) -> 0
         subtract((Succ(m), 0)) -> Succ(m)
         subtract((Succ(m), Succ(n))) -> subtract((m, n))

         main! : Host -> []
         main!(host) -> (
           (flag, n) = swap((3, True))
           user = {name: 7, age: 30, city: 2}
           bumped = older(user)
           {age, *} = bumped
           pairs = [(1, 2), (3, 4)].map(|(a, b)| a * b).fold(0, |s, x| s + x)
           host.exit!(U8.of_nat(n + flag.to_nat() + get_name(user) + age + age_of(user) + first((5, 6)) + sub(9, 4) + pairs))
         )",
        96,
    ),
    (
        "a name bound twice in a clause's head matches equal values",
        "doubled : List(Nat) -> Bool
         doubled([a, a]) -> True
         doubled(_) -> False

         same : (Nat, Nat) -> Nat
         same(n, n) if n > 0 -> 4
         same(_, _) -> 0

         paired : List((Str, Nat)) -> Nat
         paired([(key, v), (key, w), *_]) -> v + w
         paired(_) -> 0

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           two = doubled([n, n]).select(1, 0) + doubled([n, n + 1]).select(10, 0)
           host.exit!(U8.of_nat((two + same(n, n) + same(n, 2) + paired([(\"a\", n), (\"a\", 2)])) % 64))
         )",
        1 + 4 + 3,
    ),
    (
        "a guard's gap that closes ends a loop",
        "upto : (Nat, Nat) -> Nat
         upto(i, n) if i < n -> upto(Succ(i), n)
         upto(i, _) -> i

         countdown : (Nat, Nat) -> Nat
         countdown(n, total) if n > 0 -> countdown(n - 1, total + 1)
         countdown(_, total) -> total

         bisect : (Nat, Nat, Nat) -> Nat
         bisect(n, lo, hi) -> probe(n, lo, (lo + hi) / 2, hi)

         probe : (Nat, Nat, Nat, Nat) -> Nat
         probe(_, lo, mid, hi) if mid <= lo | hi <= mid -> lo
         probe(n, lo, mid, hi) if mid * mid <= n -> bisect(n, mid, hi)
         probe(n, lo, mid, _) -> bisect(n, lo, mid)

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat((upto(n, 5) + countdown(n + 2, 0) + bisect(n + 15, 0, n + 16)) % 64))
         )",
        5 + 3 + 4,
    ),
    (
        "a sift down closes the gap to its bound, once built",
        "at : (List(Nat), Nat) -> Nat
         at(xs, i) -> xs.get_or(i, 0)

         larger : (List(Nat), Nat, Nat, Nat) -> Nat
         larger(xs, a, b, n) if b < n & at(xs, a) < at(xs, b) -> b
         larger(_, a, _, _) -> a

         sift : (List(Nat), Nat, Nat) -> List(Nat)
         sift(xs, i, n) -> settle(xs, i, larger(xs, larger(xs, i, 2 * i + 1, n), 2 * i + 2, n), n)

         settle : (List(Nat), Nat, Nat, Nat) -> List(Nat)
         settle(xs, i, top, n) if i < top & top < n -> sift(xs.exchange(i, top).ok_or(xs), top, n)
         settle(xs, _, _, _) -> xs

         main! : Host -> []
         main!(host) -> (
           heap = sift([host.args.len(), 9, 4, 7, 8], 0, 5)
           host.exit!(U8.of_nat((at(heap, 0) * 10 + at(heap, 1)) % 128))
         )",
        98,
    ),
    (
        "a walk goes round on a list a call answers no longer than a part",
        "pull : (Nat, List(Nat)) -> (Nat, List(Nat))
         pull(held, []) -> (held, [])
         pull(held, [x, *rest]) -> (
           (last, others) = pull(held + x, rest)
           (last, [x + held, *others])
         )

         walk : List(Nat) -> List(Nat)
         walk([x, *rest]) -> (
           (pulled, others) = pull(x, rest)
           [pulled, *walk(others)]
         )
         walk(xs) -> xs

         shifted : List(Nat) -> Nat
         shifted([x, *rest]) -> x + shifted(rest.map(|y| y + x))
         shifted([]) -> 0

         carried : List(Nat) -> Nat
         carried([x, *rest]) -> (
           (_, moved) = rest.map_accum(x, |s, y| (s + y, s))
           x + carried(moved)
         )
         carried([]) -> 0

         kept : List(Nat) -> Nat
         kept([x, *rest]) -> x + kept(rest.filter(|y| y > x).reverse())
         kept([]) -> 0

         main! : Host -> []
         main!(host) -> (
           xs = [host.args.len(), 2, 3]
           walked = walk(xs).fold(0, |sum, x| sum + x)
           host.exit!(U8.of_nat(walked + shifted(xs) + carried(xs) + kept(xs)))
         )",
        24 + 11 + 3 + 4,
    ),
    (
        "a walk goes round on a list cut shorter than one it knows the length of",
        "merge : (List(Nat), List(Nat)) -> List(Nat)
         merge([], right) -> right
         merge(left, []) -> left
         merge([x, *xs], [y, *ys]) if x <= y -> [x, *merge(xs, [y, *ys])]
         merge(left, [y, *ys]) -> [y, *merge(left, ys)]

         sort : List(Nat) -> List(Nat)
         sort([]) -> []
         sort([x]) -> [x]
         sort(values) -> (
           (front, back) = values.split_at(values.len() / 2)
           merge(sort(front), sort(back))
         )

         tails : List(Nat) -> Nat
         tails([]) -> 0
         tails(values) -> 1 + tails(values.drop(1))

         fronts : List(Nat) -> Nat
         fronts([]) -> 0
         fronts(values) -> 1 + fronts(values.take(values.len() - 1))

         halvings : Nat -> Nat
         halvings(0) -> 0
         halvings(n) -> 1 + halvings(n / 2)

         main! : Host -> []
         main!(host) -> (
           xs = [5, host.args.len(), 4, 2, 3]
           sorted = sort(xs)
           host.exit!(U8.of_nat(sorted.get_or(0, 9) * 10 + tails(xs) + fronts(xs) + halvings(sorted.len())))
         )",
        10 + 5 + 5 + 3,
    ),
    (
        "a number a guard keeps at least ten, or one grown past a bound, ends a walk",
        "digits : (Nat, Nat) -> Nat
         digits(n, count) if n < 10 -> count + 1
         digits(n, count) -> digits(n / 10, count + 1)

         below : (Nat, Nat, Nat) -> Nat
         below(0, _, j) -> j
         below(tenths, unit, j) if tenths * 10 < unit -> below(tenths * 10, unit, j + 1)
         below(_, _, j) -> j

         hundreds : (Nat, Nat, Nat) -> Nat
         hundreds(0, _, j) -> j
         hundreds(tenths, unit, j) if tenths * 10 < unit -> hundreds(tenths * 100, unit, j + 1)
         hundreds(_, _, j) -> j

         narrow : (Nat, Nat, Nat) -> Nat
         narrow(n, low, high) if high > low + 1 -> halved(n, low, (low + high) / 2, high)
         narrow(_, _, high) -> high

         halved : (Nat, Nat, Nat, Nat) -> Nat
         halved(_, low, middle, high) if middle <= low | high <= middle -> high
         halved(n, _, middle, high) if n >= middle * middle -> narrow(n, middle, high)
         halved(n, low, middle, _) -> narrow(n, low, middle)

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(digits(12345 * n, 0) + below(n, 1000, 1) + hundreds(n, 1000, 1) + narrow(50 * n, 0, 64)))
         )",
        5 + 3 + 2 + 8,
    ),
    (
        "a parser goes round on the rest it answers inside an `Ok`",
        "Read : [Found(Nat, List(Nat)), NotFound]

         until : (List(Nat), Nat, Nat) -> Read
         until([], _, _) -> NotFound
         until([x, *rest], stop, seen) if x == stop -> Found(seen, rest)
         until([_, *rest], stop, seen) -> until(rest, stop, seen + 1)

         value : List(Nat) -> Result((Nat, List(Nat)), [Bad])
         value([]) -> Err(Bad)
         value([0, *rest]) -> list(rest, 0)
         value([x, *rest]) -> Ok((x, rest))

         list : (List(Nat), Nat) -> Result((Nat, List(Nat)), [Bad])
         list([], _) -> Err(Bad)
         list([1, *rest], total) -> Ok((total, rest))
         list(bytes, total) -> (
           (x, after) = value(bytes)?
           list(after, total + x)
         )

         skipped : List(Nat) -> Nat
         skipped([]) -> 0
         skipped([5, *rest]) -> read(until(rest, 6, 0))
         skipped([_, *rest]) -> skipped(rest) + 1

         read : Read -> Nat
         read(Found(seen, rest)) -> seen + skipped(rest)
         read(NotFound) -> 0

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           (total, _) = value([0, 2, n, 3, 1]).ok_or((0, []))
           host.exit!(U8.of_nat((total + skipped([n, 5, 7, 7, 6, n])) % 64))
         )",
        2 + (1 + 2 + 1),
    ),
    (
        "a closed row joins a wider one where answers meet",
        "merge(Absent) -> Found(1)
         merge(Found(n)) -> Found(n + 1)

         scan(0) -> Absent
         scan(Succ(n)) -> merge(scan(n))

         scanned(0) -> Bad(7)
         scanned(n) -> scan(n)

         value : [Absent, Found(Nat), Bad(Nat)] -> Nat
         value(Absent) -> 0
         value(Found(n)) -> n
         value(Bad(n)) -> n

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(value(scanned(host.args.len() + 2)) % 64))",
        3,
    ),
    (
        "a bare word on a receiver not yet known reads a field",
        "Args : Nat.(
           rest : Args -> Nat
           rest(Args(n)) -> n
         )

         count(config) -> config.rest.len() + config.size

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat((count({rest: [1, 2], size: 4}) + Args(3).rest) % 64))",
        9,
    ),
    (
        "a signature may name a function type by its alias",
        "Step = (Nat -> Nat)

         twice : (Step, Nat) -> Nat
         twice(step, n) -> step(step(n))

         bump : Step
         bump(n) -> n + 3

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(twice(bump, host.args.len()) % 64))",
        7,
    ),
    (
        "a binding takes apart a type's one constructor",
        "Memo : List(Nat)
         Pair : [Pair(Nat, Nat)]
         Box : {size: Nat, name: Str}

         step : Nat -> (Nat, Memo)
         step(n) -> (n + 1, Memo([n, n]))

         main! : Host -> []
         main!(host) -> (
           (value, Memo(entries)) = step(host.args.len())
           Pair(left, right) = Pair(value, 10)
           Box({size, *}) = Box({size: right, name: \"b\"})
           Box(whole) = Box({size: left, name: \"bb\"})
           host.exit!(U8.of_nat((value + entries.len() + size + whole.size + whole.name.len()) % 64))
         )",
        2 + 2 + 10 + 2 + 2,
    ),
    (
        "a numeral takes the word its position asks for",
        "byte : U8 -> U8
         byte(b) -> b + 250

         wide : U16 -> U16
         wide(w) -> w * 300

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(byte(10).to_nat() + wide(300).to_nat() % 256 + (0 - U64.of_nat(1)).to_nat() % 7))",
        149,
    ),
    (
        "values say themselves as text",
        "main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(1234.to_str().len() + (-56).to_str().len() * 10 + True.to_str().concat(\"x\").len() * 100))",
        22,
    ),
    (
        "a splice is its value's text",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len() + 41
           host.exit!(U8.of_nat(\"n is ${n}, big ${n > 3}, neg ${-7}!\".len() + \"${n}${n}\".len() * 10))
         )",
        66,
    ),
    (
        "strings are ordered by their bytes",
        "bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(bit(\"apple\" < \"banana\") + bit(\"ab\" < \"a\") * 2 + bit(\"x\" == \"x\") * 4))",
        5,
    ),
    (
        "bounds, written and inferred, are met by each type's own members",
        "double(x) -> x.mul(2)

         total : List(a) -> a where
           a.zero : a,
           a.add : (a, a) -> a
         total(values) -> values.fold(a.zero, |sum, value| sum.add(value))

         main! : Host -> []
         main!(host) -> (
           a = double(3) + double(U8.of_nat(200)).to_nat()
           b = [1, 2, 3].sum() + (-10 + [-1, -2].sum()).abs() + total([4, 5])
           c = [[1, 2], [3]].contains([3]).to_nat() + ([1, 2] == [1, 2]).to_nat() * 2
           host.exit!(U8.of_nat(a + b + c))
         )",
        181,
    ),
    (
        "a literal on a word or a string is an equality test",
        "verb : Str -> Nat
         verb(\"get\") -> 1
         verb(\"put\") -> 2
         verb(_) -> 0

         bytes : U8 -> Nat
         bytes(0) -> 10
         bytes(255) -> 20
         bytes(b) if b.to_nat() > 100 -> 30
         bytes(_) -> 40

         nested : Result(U8, Str) -> Nat
         nested(Ok(7)) -> 1
         nested(Err(\"x\")) -> 2
         nested(_) -> 3

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(verb(\"put\") + verb(\"post\") * 10 + bytes(255) + bytes(150) + bytes(3) + nested(Ok(7)) + nested(Err(\"x\")) * 10))",
        113,
    ),
    (
        "a record or a tuple is equal by its parts, and a tuple ordered by them",
        "weigh : (Bool, Nat) -> Nat
         weigh(True, n) -> n
         weigh(False, _) -> 0

         main! : Host -> []
         main!(host) -> (
           same = weigh((1, \"a\") == (1, \"a\"), 1) + weigh({x: 1, y: [2, 3]} == {y: [2, 3], x: 1}, 2)
           differ = weigh((1, 2) != (1, 3), 4) + weigh({x: 1, y: [2]} == {x: 1, y: [3]}, 64)
           ordered = weigh((1, (2, \"b\")) < (1, (2, \"c\")), 8) + weigh((2, 1) > (1, 9), 32) + weigh((1, 1) < (1, 1), 128)
           host.exit!(U8.of_nat(same + differ + ordered + weigh([(1, 2), (3, 4)].contains((3, 4)), 16)))
         )",
        63,
    ),
    (
        "a declared type asks for equals, cmp, to_str and hash_into by its signature alone",
        "Point : {x: Nat, y: Nat}.(
           equals : (Point, Point) -> Bool
           to_str : Point -> Str
         )

         Slot(k) : [Filled(k, Nat), Removed].(
           cmp : (Slot(k), Slot(k)) -> Order where k.cmp : (k, k) -> Order
           to_str : Slot(k) -> Str where k.to_str : k -> Str
           hash_into : (Slot(k), h) -> h where
             Hasher(h),
             k.hash_into : (k, h) -> h
         )

         filled : (Str, Nat) -> Slot(Str)
         filled(key, n) -> Filled(key, n)

         removed : Slot(Str)
         removed = Removed

         bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) -> (
           p = Point({x: 1, y: 2})
           points = bit(p == Point({y: 2, x: 1})) + bit(p != Point({x: 1, y: 3})) * 2 + bit(p.to_str() == \"{x: 1, y: 2}\") * 4
           slots = bit(filled(\"a\", 1) == filled(\"a\", 1)) * 8 + bit(filled(\"a\", 1) != removed) * 16
           ordered = bit(filled(\"a\", 2) < filled(\"b\", 1)) * 32 + bit(removed > filled(\"z\", 9)) * 64
           printed = bit(\"${[filled(\"a\", 1), removed]}\" == \"[Filled(a, 1), Removed]\") * 128
           keyed = Map.empty.insert(filled(\"a\", 1), 1).insert(removed, 2).insert(filled(\"a\", 1), 4)
           host.exit!(U8.of_nat(points + slots + ordered + printed - keyed.len() - keyed.get(removed).ok_or(0) + keyed.get(filled(\"a\", 1)).ok_or(0)))
         )",
        255 - 2 - 2 + 4,
    ),
    (
        "constraint aliases compose, each keeping its own variables",
        "import sealed {Sized}

         Additive(a) = where
           a.zero : a,
           a.add : (a, a) -> a

         Summable(a) = where
           Additive(a),
           a.to_str : a -> Str

         total : List(a) -> a where Summable(a), Additive(a)
         total(values) -> values.fold(a.zero, |sum, value| sum + value)

         Tally(r) = where
           r.fold : (r, Nat, (Nat, e) -> Nat) -> Nat

         tally : (r, e) -> Nat where Tally(r)
         tally(values, _) -> values.fold(0, |count, _| count + 1)

         Crate : [Crate(Nat)].(
           size : Crate -> Nat
           size(Crate(n)) -> n
         )

         measure : a -> Nat where Sized(a)
         measure(x) -> x.size()

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(total([1, 2, 3]) + total([-4, -5]).abs() + tally([7, 8], \"e\") + measure(Crate(20))))",
        37,
    ),
    (
        "a bound's implementation determines a variable another bound is on",
        "Person : [Person(Str)].(
           name : Person -> Str
           name(Person(name)) -> name
         )

         row : r -> Nat where
           r.fold : (r, Nat, (Nat, x) -> Nat) -> Nat,
           x.name : x -> Str
         row(items) -> items.fold(0, |total, item| total + item.name().len())

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(row([Person(\"ab\"), Person(\"cde\")])))",
        5,
    ),
    (
        "a line beginning with an infix operator goes on with the one before",
        "negated : Int -> Int
         negated(m) -> (
           k = m
           -k
         )

         main! : Host -> []
         main!(host) -> (
           n = 2
             + 3
             * 4
           big = n > 10
             & n < 20
             & negated(-7) == 7
           host.exit!(U8.of_nat(big.select(n, 0)))
         )",
        14,
    ),
    (
        "an or-pattern matches either alternative, binding the same names",
        "Shape : [Circle(Nat), Square(Nat), Dot]

         size : Shape -> Nat
         size(Circle(n) | Square(n)) -> n
         size(Dot) -> 0

         bucket : Nat -> Nat
         bucket(0) -> 0
         bucket(1 | 2) -> 1
         bucket(_) -> 2

         opens : List(Nat) -> Nat
         opens([1 | 2, *_] | [_, 3, *_]) -> 1
         opens(_) -> 0

         main! : Host -> []
         main!(host) -> (
           sizes = size(Circle(3)) + size(Square(4)) + size(Dot)
           buckets = bucket(0) + bucket(2) * 10 + bucket(7) * 100
           opened = opens([2, 9]) + opens([7, 3]) * 2 + opens([7, 4]) * 4
           host.exit!(U8.of_nat(sizes + buckets + opened))
         )",
        7 + 210 + 3,
    ),
    (
        "tags compare and print structurally, and results compare by their sides",
        "kind : Nat -> [Small, Big(Nat)]
         kind(n) if n < 10 -> Small
         kind(n) -> Big(n)

         parse : Str -> Result(Nat, [Malformed])
         parse(text) -> Nat.from_str(text)

         opens : List(Nat) -> Nat
         opens([a, b, *]) -> a + b
         opens(_) -> 0

         bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) -> (
           tags = bit(kind(3) == Small) + bit(kind(30) == Big(30)) * 2 + bit(kind(30) != Big(31)) * 4
           printed = bit(\"${kind(30)} ${kind(1)}\" == \"Big(30) Small\") * 8
           results = bit(parse(\"48\") == Ok(48)) * 16 + bit(parse(\"x\") == Err(Malformed)) * 32
           host.exit!(U8.of_nat(tags + printed + results + opens([1, 2, 9]) * 64))
         )",
        63 + 3 * 64,
    ),
    (
        "a definition is made for each callback, so a callback's own calls stop as they would alone",
        "vowels : List(U8) -> Nat
         vowels(bytes) -> bytes.count(|byte| ['a', 'e'].contains(byte))

         twice : (Nat, Nat -> Nat) -> Nat
         twice(n, f) -> f(f(n))

         shifted : (Nat, Nat -> Nat) -> Nat
         shifted(n, f) -> twice(n, |x| f(x) + 1)

         double : Nat -> Nat
         double(n) -> n * 2

         main! : Host -> []
         main!(host) -> (
           counted = vowels(['a', 'b', 'e'])
           wrapped = shifted(1, double)
           nested = [[1, 2], [3]].map(|inner| inner.map(|x| x * 10).sum()).sum()
           host.exit!(U8.of_nat(counted + wrapped * 10 + nested))
         )",
        2 + 70 + 60,
    ),
    (
        "a list's end is matched from the back, what comes before it bound whole",
        "import std.host {Host}

         ends : List(Nat) -> Nat
         ends([]) -> 0
         ends([only]) -> only
         ends([*front, a, b]) -> front.len() * 50 + a * 10 + b

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(ends([n, 2, 3, n + 3]) + ends([n + 6]) + ends([])))
         )",
        141,
    ),
    (
        "a list's end tests what it holds, and a list too short for it goes on to the next clause",
        "import std.host {Host}

         kind : List(Nat) -> Nat
         kind([*, 0]) -> 1
         kind([*, a3, _, _]) -> a3 * 10
         kind([x, *_]) -> x + 100
         kind([]) -> 3

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(kind([n, 0]) + kind([n + 4, n, n]) + kind([n, n]) + kind([])))
         )",
        155,
    ),
    (
        "a list's front and end are matched together, the middle bound whole",
        "import std.host {Host}

         shape : List(Nat) -> Nat
         shape([first, second, *middle, y, z]) -> first + second + middle.len() * 20 + y * 10 + z
         shape(_) -> 0

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           host.exit!(U8.of_nat(shape([n, 2, 3, 4, 5, n + 6]) + shape([n, 2, 3]) + shape([n, 2, 3, 4])))
         )",
        137,
    ),
    (
        "a list's end matches a range, holds any type and stands inside a tuple",
        "import std.host {Host}

         ends_in_digit : List(U8) -> Bool
         ends_in_digit([*, '0'..'9']) -> True
         ends_in_digit(_) -> False

         last_two : List(a) -> Result((a, a), [Short])
         last_two([*, a, b]) -> Ok((a, b))
         last_two(_) -> Err(Short)

         beside : ((List(Nat), Nat)) -> Nat
         beside(([*, x], y)) -> x * y
         beside(_) -> 0

         main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           digit = if ends_in_digit(['a', 'b', '7']) then 1 else 0
           letter = if ends_in_digit(['7', 'b']) then 1 else 0
           (a, b) = last_two([n, n + 1, n + 2]).ok_or((0, 0))
           (w, v) = last_two([\"x\", \"yz\"]).ok_or((\"\", \"\"))
           host.exit!(U8.of_nat(digit * 100 + letter * 50 + a * 10 + b + w.len() + v.len() + beside(([n, 4], 5)) + beside(([], 9))))
         )",
        146,
    ),
];

#[test]
fn programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        assert_eq!(Package::new(name, source).run(), *expected, "{name}");
    }
}
