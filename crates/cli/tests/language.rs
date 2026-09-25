//! The language as Ori defines it, case by case: what a program answers, or
//! why it is refused.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
    (
        "a type nothing pins is Nat",
        "main! : Host -> []
         main!(host) -> host.exit!([].len() + [[] []].len())",
        2,
    ),
    (
        "a function, a constructor and a lambda are passed into calls",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         main! : Host -> []
         main!(host) ->
           doubled = [1 2].map(twice).fold(0 |s x| s + x)
           wrapped = [3].map(Ok).map(|r| r.ok_or(0)).fold(0 |s x| s + x)
           host.exit!(doubled + wrapped)",
        9,
    ),
    (
        "an alias is its type",
        "MyError = [NotFound SomethingElse]
         Point = {x: Nat y: Nat}
         Numbers = List(Nat)

         cat : Nat -> Result(Nat MyError)
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         sum : Point -> Nat
         sum({x y}) -> x + y

         total : Numbers -> Nat
         total(xs) -> xs.fold(0 |s x| s + x)

         main! : Host -> []
         main!(host) -> host.exit!(cat(5).ok_or(0) + sum({x: 1 y: 2}) + total([4]))",
        12,
    ),
    (
        "the ordering operators are views of one cmp",
        "bit : Bool -> Nat
         bit(b) -> b.to_nat()

         main! : Host -> []
         main!(host) ->
           n = host.argc + 2
           a = bit(n < 5) + bit(n <= 3) * 2 + bit(n > 3) * 4 + bit(n >= 3) * 8
           b = bit(-2 < 1) * 16 + bit(-3 < -2) * 32 + bit(False < True) * 64 + bit(2 > 7) * 128
           host.exit!(a + b)",
        123,
    ),
    (
        "a type is ordered by defining cmp",
        "Size : [Small Large].(
           cmp : Size Size -> Order
           cmp(Small Large) -> Lt
           cmp(Large Small) -> Gt
           cmp(_ _) -> Eq
         )

         main! : Host -> []
         main!(host) -> host.exit!((Small < Large).to_nat() + (Large <= Small).to_nat() * 2)",
        1,
    ),
    (
        "? answers an Err early and joins its producers' rows",
        "cat : Nat -> Result(Nat [NotFound SomethingElse])
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         dog : Nat -> Result(Nat [Blah NotFound])
         dog(0) -> Err(NotFound)
         dog(1) -> Err(Blah)
         dog(n) -> Ok(n)

         foo : Nat -> Result(Nat [Blah NotFound SomethingElse])
         foo(n) ->
           x = cat(n)?
           y = dog(n + 1)?
           Ok(x + y)

         inline(n) -> Ok(cat(n)? + dog(n)? * 2)

         code : Result(Nat [Blah NotFound SomethingElse]) -> Nat
         code(Ok(n)) -> n
         code(Err(NotFound)) -> 100
         code(Err(SomethingElse)) -> 101
         code(Err(Blah)) -> 102

         main! : Host -> []
         main!(host) -> host.exit!(code(foo(5)) + code(foo(1)) + code(foo(0)) + code(inline(3)) - 190)",
        31,
    ),
    (
        "? in a lambda answers from the lambda",
        "half : Nat -> Result(Nat [Odd])
         half(n) if n % 2 == 0 -> Ok(n / 2)
         half(_) -> Err(Odd)

         main! : Host -> []
         main!(host) ->
           halves = [2 4].map(|n| Ok(half(n)? + 1))
           host.exit!(halves.map(|r| r.ok_or(0)).fold(0 |s x| s + x))",
        5,
    ),
    (
        "tuples, record rows, updates and destructuring",
        "swap : (Nat Bool) -> (Bool Nat)
         swap((n b)) -> (b n)

         first((k _)) -> k

         get_name : {name: Nat *} -> Nat
         get_name(r) -> r.name

         age_of(r) -> r.age

         older(r) -> {age: r.age + 1 *r}

         sub(x y) -> subtract((x y))
         subtract((0 _)) -> 0
         subtract((Succ(m) 0)) -> Succ(m)
         subtract((Succ(m) Succ(n))) -> subtract((m n))

         main! : Host -> []
         main!(host) ->
           (flag n) = swap((3 True))
           user = {name: 7 age: 30 city: 2}
           bumped = older(user)
           {age *} = bumped
           pairs = [(1 2) (3 4)].map(|(a b)| a * b).fold(0 |s x| s + x)
           host.exit!(n + flag.to_nat() + get_name(user) + age + age_of(user) + first((5 6)) + sub(9 4) + pairs)",
        96,
    ),
];

/// Programs refused, and what the message says.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "a function is not bound",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         apply() ->
           f = twice
           f(1)",
        "cannot be bound",
    ),
    (
        "a function is not answered",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         pick : Bool -> (Nat -> Nat)
         pick(_) -> twice",
        "a function is passed into a call, never answered or stored",
    ),
    (
        "a function is not answered through a type variable",
        "twice : Nat -> Nat
         twice(n) -> n * 2

         half : Nat -> Nat
         half(n) -> n / 2

         main! : Host -> []
         main!(host) -> host.exit!(True.select(twice half)(3))",
        "cannot be bound, answered, or stored",
    ),
    (
        "a function is not stored in data",
        "Handler : [Handler((Nat -> Nat))]",
        "constructor `Handler` holds a function",
    ),
    (
        "a definition with no parameters is reached with parentheses",
        "zero : Nat
         zero() -> 0

         apply : (Nat -> Nat) -> Nat
         apply(f) -> f(1)

         main! : Host -> []
         main!(host) -> host.exit!([zero].len())",
        "reached as `name()`",
    ),
    (
        "an alias does not name itself",
        "Chain = List(Chain)",
        "alias `Chain` names itself",
    ),
    (
        "an alias has no type variables",
        "Pairs = List(a)",
        "has no type variables",
    ),
    (
        "an alias takes no arguments",
        "Numbers = List(Nat)

         total : Numbers(Nat) -> Nat
         total(_) -> 0",
        "`Numbers` is an alias and takes no arguments",
    ),
    (
        "an alias owns no constructors to export",
        "exports {Numbers.*}

         Numbers = List(Nat)",
        "owns no constructors",
    ),
    (
        "a type without cmp has no order",
        "Size : [Small Large]

         main! : Host -> []
         main!(host) -> host.exit!((Small < Large).to_nat())",
        "method `cmp`",
    ),
    (
        "? admits no tag a signature does not hold",
        "dog : Nat -> Result(Nat [Blah NotFound])
         dog(0) -> Err(Blah)
         dog(n) -> Ok(n)

         bar : Nat -> Result(Nat [NotFound])
         bar(n) -> Ok(dog(n)?)",
        "`Blah` is not among the tags of `[NotFound]`",
    ),
    (
        "? answers an Err, so its definition answers a Result",
        "dog : Nat -> Result(Nat [Blah])
         dog(n) -> Ok(n)

         bar : Nat -> Nat
         bar(n) -> dog(n)?",
        "`?` answers an `Err` early, but this answers Nat",
    ),
    (
        "a tuple is not a record",
        "pair() -> (1 2)

         bad : {x: Nat} -> Nat
         bad(_) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(bad(pair()))",
        "incompatible types",
    ),
    (
        "a record without the field is refused where it is read",
        "get_name : {name: Nat *} -> Nat
         get_name(r) -> r.name

         main! : Host -> []
         main!(host) -> host.exit!(get_name({age: 3}))",
        "has no field `name`",
    ),
    (
        "an update adds no field",
        "main! : Host -> []
         main!(host) -> host.exit!({extra: 1 *{age: 3}}.age)",
        "has no field `extra`",
    ),
    (
        "a tuple's cases must be covered",
        "both : (Bool Bool) -> Nat
         both((True True)) -> 1
         both((False _)) -> 0",
        "no clause matches `both((True False))`",
    ),
];

#[test]
fn programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        assert_eq!(Package::new(name, source).run(), *expected, "{name}");
    }
}

#[test]
fn programs_are_refused_with_what_is_wrong() {
    for (name, source, expected) in REFUSED {
        let refused = Package::new(name, source).refusal();
        assert!(refused.contains(expected), "{name}: {refused}");
    }
}
