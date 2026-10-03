//! The language as Ori defines it, case by case: what a program answers.
//! Why one is refused is in `refused/`, beside the program.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
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
        "a binding shadows a name, and what follows reads the nearest",
        "main! : Host -> []
         main!(host) -> (
           n = host.args.len()
           n = n + 1
           (n, m) = (n * 10, n)
           host.exit!(U8.of_nat((n + m) % 64))
         )",
        22,
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
         total(values) -> values.fold(a.zero(), |sum, value| sum.add(value))

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
         main!(host) -> host.exit!(U8.of_nat(verb(\"put\") + verb(\"post\") * 10 + bytes(U8.of_nat(255)) + bytes(U8.of_nat(150)) + bytes(U8.of_nat(3)) + nested(Ok(U8.of_nat(7))) + nested(Err(\"x\")) * 10))",
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
         removed() -> Removed

         bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) -> (
           p = Point({x: 1, y: 2})
           points = bit(p == Point({y: 2, x: 1})) + bit(p != Point({x: 1, y: 3})) * 2 + bit(p.to_str() == \"{x: 1, y: 2}\") * 4
           slots = bit(filled(\"a\", 1) == filled(\"a\", 1)) * 8 + bit(filled(\"a\", 1) != removed()) * 16
           ordered = bit(filled(\"a\", 2) < filled(\"b\", 1)) * 32 + bit(removed() > filled(\"z\", 9)) * 64
           printed = bit(\"${[filled(\"a\", 1), removed()]}\" == \"[Filled(a, 1), Removed]\") * 128
           keyed = Map.empty().insert(filled(\"a\", 1), 1).insert(removed(), 2).insert(filled(\"a\", 1), 4)
           host.exit!(U8.of_nat(points + slots + ordered + printed - keyed.len() - keyed.get(removed()).ok_or(0) + keyed.get(filled(\"a\", 1)).ok_or(0)))
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
         total(values) -> values.fold(a.zero(), |sum, value| sum + value)

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
];

#[test]
fn programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        assert_eq!(Package::new(name, source).run(), *expected, "{name}");
    }
}
