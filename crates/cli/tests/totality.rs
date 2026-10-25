//! Which rounds of calls `faun check --totality` shows stop, read in the
//! Barb a package's expectations lower to, case by case: each extension of
//! what it reads with a program it now shows stops, and programs that do
//! not stop, or that nothing sound here shows stop, it must still list.

mod support;

use faun_core::barb;
use faun_x86_64_linux::X86_64Linux;
use support::Package;

/// Programs every round of whose calls is shown to stop.
const SHOWN: &[(&str, &str)] = &[
    (
        "a list with an element written over is as long as it was",
        "f : List(Nat) -> Nat
         f([]) -> 0
         f([x, *rest]) -> x + f(rest.put(0, x))

         expect f([1, 2, 3]) == 3",
    ),
    (
        "a list two shorter with one appended is shorter",
        "f : List(Nat) -> Nat
         f([x, _, *rest]) -> x + f(rest.append(x))
         f(_) -> 0

         expect f([1, 2, 3, 4]) == 2",
    ),
    (
        "a list two shorter with one put before it is shorter",
        "f : List(Nat) -> Nat
         f([x, _, *rest]) -> x + f([x].concat(rest))
         f(_) -> 0

         expect f([1, 2, 3]) == 2",
    ),
    (
        "a list two shorter turned round onto one is shorter",
        "f : List(Nat) -> Nat
         f([x, _, *rest]) -> x + f(rest.reverse().append(x))
         f(_) -> 0

         expect f([1, 2, 3]) == 2",
    ),
    (
        "a clause taking the last element off goes round on a shorter list",
        "total : List(Nat) -> Nat
         total([]) -> 0
         total([*init, last]) -> last + total(init)

         expect total([1, 2, 3]) == 6",
    ),
    (
        "a loop taking the last element off goes round on a shorter list",
        "total : List(Nat) -> Nat
         total(xs) -> (
           sum = 0
           s = xs
           while s is [*s, x] do (
             sum = sum + x
           )
           sum
         )

         expect total([1, 2, 3]) == 6",
    ),
    (
        "a guard read second in an and still bounds what goes round",
        "widen : (Nat, Nat) -> Nat
         widen(n, j) if n >= 2.pow(2.pow(j)) & j < n -> widen(n, j + 1)
         widen(_, j) -> 2.pow(j)

         expect widen(1000, 0) == 16",
    ),
    (
        "neither side of an or holding bounds what goes round",
        "up : (Nat, Nat) -> Nat
         up(i, n) if (i >= n | n == 7).not() -> up(i + 1, n)
         up(i, _) -> i

         expect up(0, 3) == 3",
    ),
    (
        "a loop's guard ahead of its pattern bounds what goes round",
        "count : (Nat, List(Nat)) -> Nat
         count(rounds, xs) -> (
           stack = xs
           rounds = rounds
           total = 0
           while rounds > 0 & stack is [x, *more] do (
             total = total + x
             stack = [x, *[x, *more]]
             rounds = rounds - 1
           )
           total
         )

         expect count(3, [1]) == 3",
    ),
    (
        "a guard in a loop's body bounds what goes round",
        "count : (Nat, List(Nat)) -> Nat
         count(rounds, xs) -> (
           stack = xs
           rounds = rounds
           total = 0
           while stack is [x, *more] do (
             rounds > 0 else break
             total = total + x
             stack = [x, *[x, *more]]
             rounds = rounds - 1
           )
           total
         )

         expect count(3, [1]) == 3",
    ),
    (
        "a bound guarded in the first of three clauses closes the gap",
        "mine : (List(Nat), Nat -> Bool, Nat, Nat) -> Result(Nat, [Exhausted])
         mine(_, _, candidate, limit) if candidate >= limit -> Err(Exhausted)
         mine(key, qualifies, candidate, _) if qualifies(candidate) -> Ok(candidate)
         mine(key, qualifies, candidate, limit) -> mine(key, qualifies, candidate + 1, limit)

         expect mine([], |n| n == 3, 0, 10) == Ok(3)",
    ),
    (
        "a clause taking a parameter apart after a guarded one keeps the gap",
        "sink : (List(Nat), Nat, (Nat, Nat), Nat) -> List(Nat)
         sink(entries, hole, entry, count) if hole * 2 + 1 >= count -> entries
         sink(entries, hole, entry is (key, _), count) -> (
           left = hole * 2 + 1
           if key < left then sink(entries, left, entry, count) else entries
         )

         expect sink([], 0, (1, 2), 5) == []",
    ),
    (
        "doubling from one while a power of two stays below closes the gap",
        "widen : (Nat, Nat) -> Nat
         widen(n, high is Succ(_)) if n >= 2.pow(high) -> widen(n, high * 2)
         widen(_, high) -> high

         expect widen(1000, 1) == 16",
    ),
    (
        "counting up while a tower of twos stays below closes the gap",
        "widen : (Nat, Nat) -> Nat
         widen(n, j) if n >= 2.pow(2.pow(j)) -> widen(n, j + 1)
         widen(_, j) -> 2.pow(j)

         expect widen(1000, 0) == 16",
    ),
    (
        "counting up while a power of two stays below closes the gap",
        "up : (Nat, Nat) -> Nat
         up(n, j) if n >= 2.pow(j) -> up(n, j + 1)
         up(_, j) -> j

         expect up(1000, 0) == 10",
    ),
    (
        "scaling by ten from one up to a bound closes the gap",
        "scale : (Nat, Nat) -> Nat
         scale(r, s is Succ(_)) if r >= s -> scale(r, s * 10)
         scale(_, s) -> s

         expect scale(1234, 1) == 10000",
    ),
    (
        "scaling by ten from one while ten times stays below closes the gap",
        "lower : (Nat, Nat) -> Nat
         lower(r is Succ(_), s) if r * 10 < s -> lower(r * 10, s)
         lower(r, _) -> r

         expect lower(3, 1000) == 300",
    ),
    (
        "counting up while at most a bound closes the gap",
        "upto : (Nat, Nat) -> Nat
         upto(i, n) if i <= n -> upto(i + 1, n)
         upto(i, _) -> i

         expect upto(0, 3) == 4",
    ),
    (
        "a loop split in two knows in the second what the first learned",
        "rest : Nat -> Nat
         rest(0) -> 0
         rest(left) -> on(left, left % 3)

         on : (Nat, Nat) -> Nat
         on(_, 0) -> 1
         on(left, went) -> rest(left - went)

         expect rest(10) == 1",
    ),
    (
        "a count split in two closes the gap",
        "up : (Nat, Nat) -> Nat
         up(i, n) if i < n -> step(i, n)
         up(i, _) -> i

         step : (Nat, Nat) -> Nat
         step(i, n) -> up(i + 1, n)

         expect up(0, 3) == 3",
    ),
    (
        "the first element found says the list holds one",
        "walk : List(Nat) -> Nat
         walk(xs) -> (
           xs.first() is Ok(x) else return 0
           x + walk(xs.drop(1))
         )

         expect walk([1, 2, 3]) == 6",
    ),
    (
        "the last element found says the list holds one",
        "walk : List(Nat) -> Nat
         walk(xs) -> (
           xs.last() is Ok(x) else return 0
           x + walk(xs.take(xs.len() - 1))
         )

         expect walk([1, 2, 3]) == 6",
    ),
    (
        "a list one constructor wraps is measured as the list",
        "W(a) : List(a).(
           size : W(a) -> Nat
           size(W(xs)) -> xs.len()
         )

         shrink : W(Nat) -> Nat
         shrink(W([x, *rest])) -> x + shrink(W(rest.put(0, x)))
         shrink(_) -> 0

         expect shrink(W([1, 2])) == 2",
    ),
];

/// Programs with rounds nothing shows stops, and the names in the first.
const UNSHOWN: &[(&str, &str, &str)] = &[
    (
        "a comparison that compares nothing says nothing",
        "bogus_lt : (Nat, Nat) -> Bool
         bogus_lt(_, _) -> True

         bogus : (Nat, Nat) -> Nat
         bogus(i, n) if bogus_lt(i, n) -> bogus(Succ(i), n)
         bogus(i, _) -> i",
        "bogus",
    ),
    (
        "a round rebuilding more than it took apart",
        "step : Nat -> Nat
         step(Succ(n)) -> hop(n)
         step(Zero) -> 0

         hop : Nat -> Nat
         hop(m) -> step(Succ(Succ(m)))",
        "step, hop",
    ),
    (
        "a gap a loop widens",
        "grows : (Nat, Nat) -> Nat
         grows(i, n) if i < n -> grows(i, Succ(n))
         grows(i, _) -> i",
        "grows",
    ),
    (
        "a generic definition nothing calls",
        "loop : List(a) -> Nat
         loop([]) -> 0
         loop(xs) -> loop(xs)",
        "loop",
    ),
    (
        "a guard keeping a gap where the gap stays",
        "still : (Nat, Nat) -> Nat
         still(i, n) if i < n -> still(i, n)
         still(i, _) -> i",
        "still",
    ),
    (
        "a guard read the wrong way round",
        "wrong : (Nat, Nat) -> Nat
         wrong(i, n) if i >= n -> wrong(Succ(i), n)
         wrong(i, _) -> i",
        "wrong",
    ),
    (
        "a halving that may hand on a list of one",
        "sort : List(Nat) -> List(Nat)
         sort([]) -> []
         sort(values) -> (
           (front, back) = values.split_at(values.len() / 2)
           sort(front).concat(sort(back))
         )",
        "sort",
    ),
    (
        "a library definition nothing calls",
        "spin : Nat -> Nat
         spin(n) -> spin(n)",
        "spin",
    ),
    (
        "an application definition main does not reach",
        "spin : Nat -> Nat
         spin(n) -> spin(n)

         main! : Host -> []
         main!(host) -> host.exit!(0)",
        "spin",
    ),
    (
        "a definition an expectation calls",
        "spin : Nat -> Nat
         spin(n) -> spin(n)

         expect spin(1) == 1",
        "spin",
    ),
    (
        "a parser answering what it was handed",
        "same : List(Nat) -> Result((Nat, List(Nat)), [Bad])
         same(xs) -> Ok((0, xs))

         loops : List(Nat) -> Nat
         loops([]) -> 0
         loops(xs) -> again(same(xs))

         again : Result((Nat, List(Nat)), [Bad]) -> Nat
         again(Ok((_, rest))) -> loops(rest)
         again(Err(_)) -> 0",
        "loops, again",
    ),
    (
        "a walk on a list a call grows",
        "walk : List(Nat) -> List(Nat)
         walk([x, *rest]) -> [x, *walk(rest.map(|y| y + x).append(x))]
         walk(xs) -> xs",
        "walk",
    ),
    (
        "a product by one",
        "below : (Nat, Nat, Nat) -> Nat
         below(0, _, j) -> j
         below(tenths, unit, j) if tenths * 1 < unit -> below(tenths * 1, unit, j + 1)
         below(_, _, j) -> j",
        "below",
    ),
    (
        "taking as many as a list holds",
        "walk : List(Nat) -> List(Nat)
         walk([]) -> []
         walk(values) -> walk(values.take(values.len()))",
        "walk",
    ),
    (
        "a written definition answering a type no value has",
        "unreachable : List(Nat) -> []
         unreachable(xs) -> unreachable(xs)

         absurd : [] -> Nat
         absurd(_) -> 0

         expect absurd(unreachable([1])) == 0",
        "unreachable",
    ),
    (
        "a list one shorter with one appended",
        "f : List(Nat) -> Nat
         f([x, *rest]) -> x + f(rest.append(x))
         f(_) -> 0

         expect f([]) == 0",
        "f",
    ),
    (
        "a list two shorter with two put before it",
        "f : List(Nat) -> Nat
         f([x, y, *rest]) -> x + f([x, y].concat(rest))
         f(_) -> 0

         expect f([]) == 0",
        "f",
    ),
    (
        "a list one shorter with one put after it",
        "f : List(Nat) -> Nat
         f([x, *rest]) -> x + f(rest.concat([x]))
         f(_) -> 0

         expect f([]) == 0",
        "f",
    ),
    (
        "a list one shorter turned round with one appended",
        "f : List(Nat) -> Nat
         f([x, *rest]) -> x + f(rest.reverse().append(x))
         f(_) -> 0

         expect f([]) == 0",
        "f",
    ),
    (
        "a list with an element written over",
        "f : List(Nat) -> Nat
         f(xs is [x, *_]) -> x + f(xs.put(0, x + 1))
         f(_) -> 0

         expect f([]) == 0",
        "f",
    ),
    (
        "a list with its last element taken off and put back",
        "total : List(Nat) -> Nat
         total([]) -> 0
         total([*init, last]) -> last + total(init.append(last))

         expect total([]) == 0",
        "total",
    ),
    (
        "a list whose last element was found",
        "total : List(Nat) -> Nat
         total([]) -> 0
         total(whole is [*_, last]) -> last + total(whole)

         expect total([]) == 0",
        "total",
    ),
    (
        "the front of a list split at its length",
        "front : List(Nat) -> Nat
         front(xs) -> (
           (init, _) = xs.split_at(xs.len())
           if xs is [] then 0 else front(init)
         )

         expect front([]) == 0",
        "front",
    ),
    (
        "a guard in an and read the wrong way round",
        "up : (Nat, Nat) -> Nat
         up(i, n) if n > 0 & i >= n -> up(i + 1, n)
         up(i, _) -> i

         expect up(0, 3) == 0",
        "up",
    ),
    (
        "a guard either side of an or",
        "up : (Nat, Nat) -> Nat
         up(i, n) if i < n | n < i -> up(i + 1, n)
         up(i, _) -> i

         expect up(0, 3) == 3",
        "up",
    ),
    (
        "a guard on one side of an or",
        "up : (Nat, Nat) -> Nat
         up(i, n) if n > 5 | i < n -> up(i + 1, n)
         up(i, _) -> i

         expect up(0, 3) == 3",
        "up",
    ),
    (
        "a guard negated over an and",
        "up : (Nat, Nat) -> Nat
         up(i, n) if (i < n & n > 5).not() -> up(i + 1, n)
         up(i, _) -> i

         expect up(0, 0) == 0",
        "up",
    ),
    (
        "a guard in an and where the gap widens",
        "up : (Nat, Nat) -> Nat
         up(i, n) if n > 5 & i < n -> up(i, n + 1)
         up(i, _) -> i

         expect up(0, 3) == 0",
        "up",
    ),
    (
        "a loop's guard ahead of its pattern saying nothing",
        "count : (Nat, List(Nat)) -> Nat
         count(rounds, xs) -> (
           stack = xs
           rounds = rounds
           total = 0
           while rounds >= 0 & stack is [x, *more] do (
             total = total + x
             stack = [x, *[x, *more]]
             rounds = rounds - 1
           )
           total
         )

         expect count(0, []) == 0",
        "count, going on",
    ),
    (
        "a loop's guard after its pattern read the wrong way round",
        "count : (Nat, List(Nat)) -> Nat
         count(rounds, xs) -> (
           stack = xs
           rounds = rounds
           total = 0
           while stack is [x, *more] & rounds < 5 do (
             total = total + x
             stack = [x, *[x, *more]]
             rounds = rounds - 1
           )
           total
         )

         expect count(0, []) == 0",
        "count, going on",
    ),
    (
        "a bound guarded the wrong way round in the first of three clauses",
        "mine : (List(Nat), Nat -> Bool, Nat, Nat) -> Result(Nat, [Exhausted])
         mine(_, _, candidate, limit) if candidate < limit -> Err(Exhausted)
         mine(key, qualifies, candidate, _) if qualifies(candidate) -> Ok(candidate)
         mine(key, qualifies, candidate, limit) -> mine(key, qualifies, candidate + 1, limit)

         expect mine([], |n| n == 3, 0, 10) == Err(Exhausted)",
        "mine, mine, going on",
    ),
    (
        "a clause taking a parameter apart after a guard the wrong way round",
        "sink : (List(Nat), Nat, (Nat, Nat), Nat) -> List(Nat)
         sink(entries, hole, entry, count) if hole * 2 + 1 < count -> entries
         sink(entries, hole, entry is (key, _), count) -> (
           left = hole * 2 + 1
           if key < left then sink(entries, left, entry, count) else entries
         )

         expect sink([], 0, (1, 2), 5) == []",
        "sink, sink, going on",
    ),
    (
        "a clause taking a list apart after a guard the wrong way round",
        "up : (Nat, Nat, List(Nat)) -> Nat
         up(i, n, _) if i < n -> i
         up(i, n, []) -> i
         up(i, n, [x, *rest]) -> up(i + 1, n, [x, *rest])

         expect up(0, 5, [1]) == 0",
        "up, up, going on",
    ),
    (
        "doubling what may be nought",
        "widen : (Nat, Nat) -> Nat
         widen(n, high) if n >= 2.pow(high) -> widen(n, high * 2)
         widen(_, high) -> high

         expect widen(1000, 1) == 16",
        "widen",
    ),
    (
        "multiplying by one while a power stays below",
        "widen : (Nat, Nat) -> Nat
         widen(n, high is Succ(_)) if n >= 2.pow(high) -> widen(n, high * 1)
         widen(_, high) -> high

         expect widen(0, 1) == 1",
        "widen",
    ),
    (
        "doubling while a power of one stays below",
        "widen : (Nat, Nat) -> Nat
         widen(n, high is Succ(_)) if n >= 1.pow(high) -> widen(n, high * 2)
         widen(_, high) -> high

         expect widen(0, 1) == 1",
        "widen",
    ),
    (
        "counting up while a power of what may be one stays below",
        "up : (Nat, Nat, Nat) -> Nat
         up(n, b, j) if n >= b.pow(j) -> up(n, b, j + 1)
         up(_, _, j) -> j

         expect up(1000, 2, 0) == 10",
        "up",
    ),
    (
        "scaling by ten what may be nought",
        "scale : (Nat, Nat) -> Nat
         scale(r, s) if r >= s -> scale(r, s * 10)
         scale(_, s) -> s

         expect scale(1234, 1) == 10000",
        "scale",
    ),
    (
        "scaling by ten what may be nought while ten times stays below",
        "lower : (Nat, Nat) -> Nat
         lower(r, s) if r * 10 < s -> lower(r * 10, s)
         lower(r, _) -> r

         expect lower(3, 1000) == 300",
        "lower",
    ),
    (
        "a gap in order where nothing moves",
        "upto : (Nat, Nat) -> Nat
         upto(i, n) if i <= n -> upto(i, n)
         upto(i, _) -> i

         expect upto(5, 3) == 5",
        "upto",
    ),
    (
        "a gap in order where both ends move up",
        "upto : (Nat, Nat) -> Nat
         upto(i, n) if i <= n -> upto(i + 1, n + 1)
         upto(i, _) -> i

         expect upto(5, 3) == 5",
        "upto",
    ),
    (
        "a gap one past its end where nothing moves",
        "upto : (Nat, Nat) -> Nat
         upto(i, n) if i <= n + 1 -> upto(i, n)
         upto(i, _) -> i

         expect upto(5, 3) == 5",
        "upto",
    ),
    (
        "a loop split in two where the second may take nothing",
        "rest : Nat -> Nat
         rest(0) -> 0
         rest(left) -> on(left, left % 3)

         on : (Nat, Nat) -> Nat
         on(0, _) -> 1
         on(left, went) -> rest(left - went)

         expect rest(0) == 0",
        "rest, on",
    ),
    (
        "a loop split in two whose second is called from outside",
        "rest : Nat -> Nat
         rest(left) -> on(left, 1)

         on : (Nat, Nat) -> Nat
         on(_, 0) -> 1
         on(left, went) -> rest(left - went)

         expect on(0, 1) == 1",
        "on, rest",
    ),
    (
        "a count split in two where nothing moves",
        "up : (Nat, Nat) -> Nat
         up(i, n) if i < n -> step(i, n)
         up(i, _) -> i

         step : (Nat, Nat) -> Nat
         step(i, n) -> up(i, n)

         expect up(3, 3) == 3",
        "up, step",
    ),
    (
        "a count split in three where nothing moves",
        "up : (Nat, Nat) -> Nat
         up(i, n) if i < n -> step(i, n)
         up(i, _) -> i

         step : (Nat, Nat) -> Nat
         step(i, n) -> again(i, n)

         again : (Nat, Nat) -> Nat
         again(i, n) -> up(i, n)

         expect up(3, 3) == 3",
        "up, step, again",
    ),
    (
        "a count split in two where both ends move up",
        "up : (Nat, Nat) -> Nat
         up(i, n) if i < n -> step(i, n)
         up(i, _) -> i

         step : (Nat, Nat) -> Nat
         step(i, n) -> up(i + 1, n + 1)

         expect up(3, 3) == 3",
        "up, step",
    ),
    (
        "a number bound after the call going round",
        "up : (Nat, Nat) -> Nat
         up(i, n) -> (
           a = if n > 0 then up(i + 1, n) else i
           k = 7
           a + k
         )

         expect up(0, 0) == 7",
        "up",
    ),
    (
        "a number bound after a call read in place",
        "up : (Nat, Nat) -> Nat
         up(i, n) -> (
           a = if n > 0 then step(i, n) else i
           k = 7
           a + k
         )

         step : (Nat, Nat) -> Nat
         step(i, n) -> up(i + 1, n)

         expect up(0, 0) == 7",
        "up, step",
    ),
    (
        "a field of an argument read in place",
        "first : ((Nat, Nat)) -> Nat
         first((x, _)) -> x

         spin : ((Nat, Nat), (Nat, Nat)) -> Nat
         spin((Succ(_), _), p1) -> (
           x = first(p1)
           if x is Succ(y) then spin((y, 0), p1) else 0
         )
         spin(_, _) -> 0

         expect spin((0, 0), (0, 0)) == 0",
        "spin",
    ),
    (
        "a guard's answer handed to a body read in place",
        "less : (Nat, Nat, Bool) -> Nat
         less(k, _, True) -> k - 1
         less(k, _, False) -> k

         spin : (Nat, Nat, Nat) -> Nat
         spin(n, i, k is Succ(j)) -> (
           below = i < n
           spin(n, i, less(k, j, below))
         )
         spin(_, _, _) -> 0

         expect spin(0, 0, 0) == 0",
        "spin",
    ),
    (
        "a loop's guard after a pattern bounding nothing it hands on",
        "spin : (Result(Nat, Nat), Nat) -> Nat
         spin(r, i) -> (
           r = r
           while r is Ok(a) & i < 100 do (
             r = Ok(if a < i then i else i)
           )
           i
         )

         expect spin(Err(0), 0) == 0",
        "spin, going on",
    ),
    (
        "an answer the empty list gives too",
        "fake : List(Nat) -> Result(Nat, [Empty])
         fake([]) -> Ok(0)
         fake([x, *_]) -> Ok(x)

         walk : List(Nat) -> Nat
         walk(xs) -> (
           fake(xs) is Ok(x) else return 0
           x + walk(xs.take(xs.len() - 1))
         )

         expect walk([]) == 0",
        "walk",
    ),
    (
        "an answer only the empty list gives, gone on past the other",
        "check : List(Nat) -> Result(Nat, [Empty])
         check([]) -> Ok(0)
         check([x, *_]) -> Err(Empty)

         walk : List(Nat) -> Nat
         walk(xs) -> (
           check(xs) is Ok(x) else return 0
           x + walk(xs.take(xs.len() - 1))
         )

         expect walk([1]) == 0",
        "walk",
    ),
    (
        "the first element found and the whole list handed on",
        "walk : List(Nat) -> Nat
         walk(xs) -> (
           xs.first() is Ok(x) else return 0
           x + walk(xs.put(0, x))
         )

         expect walk([]) == 0",
        "walk",
    ),
    (
        "a list one constructor wraps grown",
        "W(a) : List(a).(
           size : W(a) -> Nat
           size(W(xs)) -> xs.len()
         )

         grow : W(Nat) -> Nat
         grow(W([x, *rest])) -> grow(W([x, x, *rest]))
         grow(_) -> 0

         expect grow(W([])) == 0",
        "grow",
    ),
];

/// The names of each pure round nothing shows stops in `source`, as the
/// command lists them.
fn unshown(name: &str, source: &str) -> Vec<String> {
    let package = Package::new(name, source);
    let tests = faun::lower_tests_to_barb(&package.entry(), &X86_64Linux)
        .unwrap_or_else(|error| panic!("{name}: {}", error.message));
    let program = tests.barb;
    let mut rounds = Vec::new();
    for round in barb::unproved(&program) {
        if !round.pure {
            continue;
        }
        let mut names: Vec<&str> = Vec::new();
        for id in &round.functions {
            let written = program.name(program.function(*id).name);
            if !names.contains(&written) {
                names.push(written);
            }
        }
        rounds.push(names.join(", "));
    }
    rounds
}

#[test]
fn every_round_these_programs_go_round_is_shown_to_stop() {
    std::thread::scope(|scope| {
        let cases: Vec<_> = SHOWN
            .iter()
            .map(|&(name, source)| (name, scope.spawn(move || unshown(name, source))))
            .collect();
        for (name, case) in cases {
            let rounds = case.join().expect("a case to be read");
            assert!(rounds.is_empty(), "{name}: {rounds:?}");
        }
    });
}

#[test]
fn a_round_nothing_shows_stops_is_listed() {
    std::thread::scope(|scope| {
        let cases: Vec<_> = UNSHOWN
            .iter()
            .map(|&(name, source, first)| (name, first, scope.spawn(move || unshown(name, source))))
            .collect();
        for (name, first, case) in cases {
            let rounds = case.join().expect("a case to be read");
            assert_eq!(
                rounds.first().map(String::as_str),
                Some(first),
                "{name}: {rounds:?}"
            );
        }
    });
}
