//! Structural tags and nominal constructors, as Ori has them. A tag exists
//! by being written and belongs to no module; rows of tags join where they
//! meet; a signature's row is closed for its body and open to its callers;
//! a word a declaration also claims is read as its position's type decides.
//! Each case is a Faun package, lowered for x86-64 and run on the reference
//! interpreter; those refused are in `refused/`.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
    (
        "failures from two producers join in one row",
        "cat : Nat -> Result(Nat, [NotFound, SomethingElse])
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         dog : Nat -> Result(Nat, [Blah, NotFound])
         dog(0) -> Err(NotFound)
         dog(1) -> Err(Blah)
         dog(n) -> Ok(n)

         pick : (Bool, Nat) -> Result(Nat, [Blah, NotFound, SomethingElse])
         pick(True, n) -> cat(n)
         pick(False, n) -> dog(n)

         code : Result(Nat, [Blah, NotFound, SomethingElse]) -> Nat
         code(Ok(n)) -> n
         code(Err(NotFound)) -> 100
         code(Err(SomethingElse)) -> 101
         code(Err(Blah)) -> 102

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(pick(False, 1)) + code(pick(True, 0)) - 200))",
        2,
    ),
    (
        "an unsigned match with a catch-all takes tags it does not name",
        "f(A) -> 1
         f(B(n)) -> n
         f(_) -> 7

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(f(C) + f(B(3)) + f(A)))",
        11,
    ),
    (
        "a closed row answered where a caller widens it is widened",
        "same : [A, B] -> [A, B]
         same(x) -> x

         code : [A, B, C] -> Nat
         code(A) -> 1
         code(B) -> 2
         code(C) -> 3

         pick : Bool -> [A, B, C]
         pick(True) -> same(B)
         pick(False) -> C

         kept : List([A, B]) -> List([A, B])
         kept(xs) -> xs

         main! : Host -> []
         main!(host) ->
           listed = kept([A, B]).map(|x| code(x)).fold(0, |s, x| s + x)
           host.exit!(U8.of_nat(code(pick(True)) * 10 + code(pick(False)) + listed * 50))",
        173,
    ),
    (
        "a row inside a tag is widened with it",
        "wrap : Result(Nat, [Empty]) -> Result(Nat, [Outer([Empty])])
         wrap(Ok(n)) -> Ok(n)
         wrap(Err(e)) -> Err(Outer(e))

         unwrap(Err(Outer(Empty))) -> 5
         unwrap(Ok(n)) -> n

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(unwrap(wrap([7].take(0).first())) + unwrap(wrap([7].first()))))",
        12,
    ),
    (
        "a lambda matches the tag a library answers",
        "main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat([1, 2].get(5).map_err(|OutOfBounds| 9).err_or(0)))",
        9,
    ),
    (
        "one word is a tag or a constructor as its position decides",
        "Light : [Low, High].(
           brightness : Light -> Nat
           brightness(Low) -> 1
           brightness(High) -> 10
         )

         lift : [Low, Found(Nat)] -> Light
         lift(Low) -> Low
         lift(Found(_)) -> High

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(lift(Low).brightness() + lift(Found(3)).brightness() * 2))",
        21,
    ),
    (
        "two types may each declare a word",
        "Match : [Failed(Nat), Matched]
         Parse : [Failed(Nat), Parsed]

         blame : Match -> Parse
         blame(Failed(m)) -> Failed(m + 1)
         blame(Matched) -> Parsed

         code : Parse -> Nat
         code(Failed(n)) -> n
         code(Parsed) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(blame(Failed(4)))))",
        5,
    ),
    (
        "a qualified constructor names its type outright",
        "Match : [Failed(Nat), Matched]
         Parse : [Failed(Nat), Parsed]

         pick(n) -> Parse.Failed(n)

         code(Parse.Failed(n)) -> n
         code(Parse.Parsed) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(pick(9))))",
        9,
    ),
    (
        "a word a module keeps private is free for others to write as a tag",
        "import sealed {Failure}

         code : [NotFound, Other] -> Nat
         code(NotFound) -> 3
         code(Other) -> 4

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(NotFound)))",
        3,
    ),
    (
        "a tag where a function is wanted builds the tag from its fields",
        "cat : Nat -> Result(Nat, [NotFound])
         cat(0) -> Err(NotFound)
         cat(n) -> Ok(n)

         code : Result(Nat, [CatFailure([NotFound])]) -> Nat
         code(Ok(n)) -> n
         code(Err(CatFailure(NotFound))) -> 7

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(cat(0).map_err(CatFailure)) + code(cat(3).map_err(CatFailure)) + [1, 2].map(Boxed).len()))",
        12,
    ),
    (
        "a result bound before `?` answers its error at the wider row",
        "narrow : Nat -> Result(Nat, [A])
         narrow(0) -> Err(A)
         narrow(n) -> Ok(n)

         wide : Nat -> Result(Nat, [B, A])
         wide(n) ->
           taken = narrow(n)
           kept = taken?
           Ok(kept)

         code : Result(Nat, [B, A]) -> Nat
         code(Ok(n)) -> n % 10
         code(Err(A)) -> 50
         code(Err(B)) -> 60

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(wide(host.args.len() - 1)) + code(wide(7))))",
        57,
    ),
    (
        "a signature's `_` is the row its clauses fail with",
        "half : Nat -> Result(Nat, [Odd])
         half(n) if n % 2 == 0 -> Ok(n / 2)
         half(_) -> Err(Odd)

         small : Nat -> Result(Nat, [Big])
         small(n) if n < 10 -> Ok(n)
         small(_) -> Err(Big)

         both : Nat -> Result(Nat, _)
         both(n) -> small(half(n)?)

         code : Result(Nat, [Odd, Big]) -> Nat
         code(Ok(n)) -> n
         code(Err(Odd)) -> 10
         code(Err(Big)) -> 20

         main! : Host -> []
         main!(host) -> host.exit!(U8.of_nat(code(both(8)) + code(both(3)) + code(both(40))))",
        34,
    ),
];

#[test]
fn tag_programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        let package = Package::new(name, source);
        assert_eq!(package.run(), *expected, "{name}");
    }
}
