//! Structural tags and nominal constructors, as Ori has them. A tag exists
//! by being written and belongs to no module; rows of tags join where they
//! meet; a signature's row is closed for its body and open to its callers;
//! a word a declaration also claims is read as its position's type decides.
//! Each case is a Faun package, lowered for x86-64 and run on the reference
//! interpreter, or refused with the message it names.

mod support;

use support::Package;

/// Programs and the status each exits with.
const RUNNING: &[(&str, &str, u32)] = &[
    (
        "failures from two producers join in one row",
        "cat : Nat -> Result(Nat [NotFound SomethingElse])
         cat(0) -> Err(NotFound)
         cat(1) -> Err(SomethingElse)
         cat(n) -> Ok(n)

         dog : Nat -> Result(Nat [Blah NotFound])
         dog(0) -> Err(NotFound)
         dog(1) -> Err(Blah)
         dog(n) -> Ok(n)

         pick : Bool Nat -> Result(Nat [Blah NotFound SomethingElse])
         pick(True n) -> cat(n)
         pick(False n) -> dog(n)

         code : Result(Nat [Blah NotFound SomethingElse]) -> Nat
         code(Ok(n)) -> n
         code(Err(NotFound)) -> 100
         code(Err(SomethingElse)) -> 101
         code(Err(Blah)) -> 102

         main! : Host -> []
         main!(host) -> host.exit!(code(pick(False 1)) + code(pick(True 0)) - 200)",
        2,
    ),
    (
        "an unsigned match with a catch-all takes tags it does not name",
        "f(A) -> 1
         f(B(n)) -> n
         f(_) -> 7

         main! : Host -> []
         main!(host) -> host.exit!(f(C) + f(B(3)) + f(A))",
        11,
    ),
    (
        "a closed row answered where a caller widens it is widened",
        "same : [A B] -> [A B]
         same(x) -> x

         code : [A B C] -> Nat
         code(A) -> 1
         code(B) -> 2
         code(C) -> 3

         pick : Bool -> [A B C]
         pick(True) -> same(B)
         pick(False) -> C

         kept : List([A B]) -> List([A B])
         kept(xs) -> xs

         main! : Host -> []
         main!(host) ->
           listed = kept([A B]).map(|x| code(x)).fold(0 |s x| s + x)
           host.exit!(code(pick(True)) * 10 + code(pick(False)) + listed * 50)",
        173,
    ),
    (
        "a row inside a tag is widened with it",
        "wrap : Result(Nat [Empty]) -> Result(Nat [Outer([Empty])])
         wrap(Ok(n)) -> Ok(n)
         wrap(Err(e)) -> Err(Outer(e))

         unwrap(Err(Outer(Empty))) -> 5
         unwrap(Ok(n)) -> n

         main! : Host -> []
         main!(host) -> host.exit!(unwrap(wrap([7].take(0).first())) + unwrap(wrap([7].first())))",
        12,
    ),
    (
        "a lambda matches the tag a library answers",
        "main! : Host -> []
         main!(host) -> host.exit!([1 2].get(5).map_err(|OutOfBounds| 9).err_or(0))",
        9,
    ),
    (
        "one word is a tag or a constructor as its position decides",
        "Light : [Low High].(
           brightness : Light -> Nat
           brightness(Low) -> 1
           brightness(High) -> 10
         )

         lift : [Low Found(Nat)] -> Light
         lift(Low) -> Low
         lift(Found(_)) -> High

         main! : Host -> []
         main!(host) -> host.exit!(lift(Low).brightness() + lift(Found(3)).brightness() * 2)",
        21,
    ),
    (
        "two types may each declare a word",
        "Match : [Failed(Nat) Matched]
         Parse : [Failed(Nat) Parsed]

         blame : Match -> Parse
         blame(Failed(m)) -> Failed(m + 1)
         blame(Matched) -> Parsed

         code : Parse -> Nat
         code(Failed(n)) -> n
         code(Parsed) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(code(blame(Failed(4))))",
        5,
    ),
    (
        "a qualified constructor names its type outright",
        "Match : [Failed(Nat) Matched]
         Parse : [Failed(Nat) Parsed]

         pick(n) -> Parse.Failed(n)

         code(Parse.Failed(n)) -> n
         code(Parse.Parsed) -> 0

         main! : Host -> []
         main!(host) -> host.exit!(code(pick(9)))",
        9,
    ),
    (
        "a word a module keeps private is free for others to write as a tag",
        "import sealed {Failure}

         code : [NotFound Other] -> Nat
         code(NotFound) -> 3
         code(Other) -> 4

         main! : Host -> []
         main!(host) -> host.exit!(code(NotFound))",
        3,
    ),
];

/// Programs refused, and what the message says.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "a body answers a tag its signature does not hold",
        "first : List(a) -> Result(a [Empty])
         first([]) -> Err(Nope)
         first([h *_]) -> Ok(h)",
        "`Nope` is not among the tags of `[Empty]`",
    ),
    (
        "clauses naming every tag close their row to callers",
        "f(A) -> 1
         f(B) -> 2

         main! : Host -> []
         main!(host) -> host.exit!(f(C))",
        "`C` is not among the tags of `[A B]`",
    ),
    (
        "a signature's row must be covered",
        "g : [A B C] -> Nat
         g(A) -> 1
         g(B) -> 2",
        "no clause matches `g(C)`",
    ),
    (
        "a tag inside a constructor must be covered",
        "describe : Result(Nat [Missing Invalid(Nat)]) -> Nat
         describe(Ok(n)) -> n
         describe(Err(Missing)) -> 1",
        "no clause matches `describe(Err(Invalid(_)))`",
    ),
    (
        "a word two types claim with nothing to decide is ambiguous",
        "Match : [Failed(Nat) Matched]
         Parse : [Failed(Nat) Parsed]

         orphan(m) -> Failed(m)",
        "nothing decides between `Match.Failed` and `Parse.Failed`",
    ),
    (
        "inside a block, the block's word is its own constructor",
        "Parse : [Failed(Nat) Parsed]
         Match : [Failed(Nat) Matched].(
           wrong : Nat -> Parse
           wrong(n) -> Failed(n)
         )",
        "inside `Match`'s block, the bare `Failed` reads as `Match`'s own constructor",
    ),
    (
        "a structural tag cannot forge a sealed type",
        "import sealed {Failure accept}

         main! : Host -> []
         main!(host) -> host.exit!(accept(NotFound))",
        "Failure -> Nat and [NotFound *]",
    ),
    (
        "a sealed constructor is not reached by qualifying it",
        "import sealed {Failure}

         leak : Failure
         leak() -> Failure.NotFound",
        "type `Failure` has no constructor `NotFound` visible here",
    ),
];

#[test]
fn tag_programs_answer_what_they_say() {
    for (name, source, expected) in RUNNING {
        let package = Package::new(name, source);
        assert_eq!(package.run(), *expected, "{name}");
    }
}

#[test]
fn tag_programs_are_refused_with_what_is_wrong() {
    for (name, source, expected) in REFUSED {
        let package = Package::new(name, source);
        let refused = package.refusal();
        assert!(refused.contains(expected), "{name}: {refused}");
    }
}
