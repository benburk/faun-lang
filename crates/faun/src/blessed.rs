//! The small syntax-to-prelude contract for literals.
//!
//! These are not runtime intrinsics. Numerals remain ordinary `Nat` values;
//! an `Int` literal calls the library's `of_nat` and optional `neg`, while a
//! string literal is permitted to construct the private `Str`/`List`/`U8`
//! representation. Canonical identities are discovered once from the loaded
//! standard package instead of compared by spelling throughout later passes.

use std::fmt;

use faun_core::float::Operation;
use num_bigint::BigUint;

use super::modules::{LoadedProgram, TypeBinding};
use super::{Symbol, Symbols};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreludeIds {
    pub bool_: Symbol,
    pub nat: Symbol,
    pub int: Symbol,
    pub str_: Symbol,
    pub u8_: Symbol,
    pub list: Symbol,
    pub int_of_nat: Symbol,
    pub int_neg: Symbol,
    pub bool_not: Symbol,
    pub bool_false: Symbol,
    pub bool_true: Symbol,
    pub str_constructor: Symbol,
    /// How an interpolated string's pieces are joined.
    pub str_concat: Symbol,
    /// What a string pattern is tested with.
    pub str_equals: Symbol,
    /// How a clause's tests are joined with its guard.
    pub bool_and: Symbol,
    pub u8_constructor: Symbol,
    pub list_nil: Symbol,
    pub list_cons: Symbol,
    /// A comparison's answer, and the fixed view of it each ordering
    /// operator reads: `<` is `lt`, `<=` is `le`, and so on.
    pub order: Symbol,
    pub order_lt: Symbol,
    pub order_le: Symbol,
    pub order_gt: Symbol,
    pub order_ge: Symbol,
    /// How a tuple's `cmp` goes on past an equal position.
    pub order_then: Symbol,
    pub order_eq: Symbol,
    /// The spellings of the members a closed record, a tuple or a tag row
    /// has without declaring them, where anything spells them.
    pub equals: Option<Symbol>,
    pub cmp: Option<Symbol>,
    pub to_str: Option<Symbol>,
    /// What `?` takes apart and answers with.
    pub result: Symbol,
    pub result_ok: Symbol,
    pub result_err: Symbol,
    /// The fixed-width words a numeral may be, each built with its `of_nat`.
    pub words: Vec<Word>,
    /// The floats a decimal numeral may be, each built with its
    /// `of_decimal`, the first the one nothing else decides.
    pub floats: Vec<Float>,
}

/// A prelude float a decimal numeral may be: the type, how `digits /
/// 10^scale` becomes one, and how it is negated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Float {
    pub ty: Symbol,
    pub name: String,
    pub of_decimal: Symbol,
    pub neg: Symbol,
    /// Its format, and the methods that compute an IEEE 754 operation of
    /// it, which Barb is told of; see `faun_core::barb::Program::claim`.
    pub format: faun_core::float::Format,
    pub operations: Vec<(Symbol, Operation)>,
}

/// A prelude word a numeral may be: the type, how a natural becomes one,
/// and the numerals it takes, which its module declares as
/// `numerals_below`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Word {
    pub ty: Symbol,
    pub name: String,
    pub of_nat: Symbol,
    /// What a numeral pattern of the word is tested with.
    pub equals: Symbol,
    pub below: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreludeError {
    pub message: String,
}

impl fmt::Display for PreludeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for PreludeError {}

impl PreludeIds {
    /// Locate and validate identities needed by literal syntax.
    ///
    /// Private wrapper constructors are read from their defining module, not
    /// its public interface. This is the precise privilege string syntax has.
    ///
    /// # Errors
    ///
    /// Reports the first missing standard type, constructor, or method.
    #[expect(
        clippy::too_many_lines,
        reason = "one standard identity per line, in the order the struct declares them"
    )]
    pub fn find_in(program: &LoadedProgram) -> Result<Self, PreludeError> {
        let bool_ = binding(program, "Bool")?;
        let nat = binding(program, "Nat")?;
        let int = binding(program, "Int")?;
        let str_ = binding_with_private_constructor(program, "Str")?;
        let u8_ = binding_with_private_constructor(program, "U8")?;
        let list = binding(program, "List")?;
        let order = binding(program, "Order")?;
        let result = binding(program, "Result")?;
        let words = ["U8", "U16", "U32", "U64"]
            .into_iter()
            .filter_map(|name| word(program, name))
            .collect();
        let floats = ["F64", "F32"]
            .into_iter()
            .filter_map(|name| {
                let binding = binding(program, name).ok()?;
                let operations = [
                    ("add", Operation::Add),
                    ("sub", Operation::Sub),
                    ("mul", Operation::Mul),
                    ("div", Operation::Div),
                    ("sqrt", Operation::Sqrt),
                ]
                .into_iter()
                .filter_map(|(spelled, operation)| {
                    Some((method(program, &binding, name, spelled).ok()?, operation))
                })
                .collect();
                Some(Float {
                    ty: binding.canonical,
                    name: name.to_owned(),
                    of_decimal: method(program, &binding, name, "of_decimal").ok()?,
                    neg: method(program, &binding, name, "neg").ok()?,
                    format: if name == "F32" {
                        faun_core::float::Format::Binary32
                    } else {
                        faun_core::float::Format::Binary64
                    },
                    operations,
                })
            })
            .collect();
        Ok(Self {
            bool_: bool_.canonical,
            nat: nat.canonical,
            int: int.canonical,
            str_: str_.canonical,
            u8_: u8_.canonical,
            list: list.canonical,
            int_of_nat: method(program, &int, "Int", "of_nat")?,
            int_neg: method(program, &int, "Int", "neg")?,
            bool_not: method(program, &bool_, "Bool", "not")?,
            bool_false: constructor(program, &bool_, "Bool", "False")?,
            bool_true: constructor(program, &bool_, "Bool", "True")?,
            str_constructor: constructor(program, &str_, "Str", "Str")?,
            str_concat: method(program, &str_, "Str", "concat")?,
            str_equals: method(program, &str_, "Str", "equals")?,
            bool_and: method(program, &bool_, "Bool", "and")?,
            u8_constructor: constructor(program, &u8_, "U8", "U8")?,
            list_nil: constructor(program, &list, "List", "Nil")?,
            list_cons: constructor(program, &list, "List", "Cons")?,
            order: order.canonical,
            order_lt: method(program, &order, "Order", "lt")?,
            order_le: method(program, &order, "Order", "le")?,
            order_gt: method(program, &order, "Order", "gt")?,
            order_ge: method(program, &order, "Order", "ge")?,
            order_then: method(program, &order, "Order", "then")?,
            order_eq: constructor(program, &order, "Order", "Eq")?,
            equals: program.symbols.find("equals"),
            cmp: program.symbols.find("cmp"),
            to_str: program.symbols.find("to_str"),
            result: result.canonical,
            result_ok: constructor(program, &result, "Result", "Ok")?,
            result_err: constructor(program, &result, "Result", "Err")?,
            words,
            floats,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumeralType<'a> {
    Nat,
    Int,
    Word(&'a Word),
}

/// Literal-focused core syntax. It is independent of the surface tree so type
/// inference can decide a numeral first and Barb lowering can consume the
/// result without knowing source spellings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralExpr {
    Natural(BigUint),
    Construct(Symbol, Vec<Self>),
    Call(Symbol, Vec<Self>),
}

/// A decimal numeral, `digits / 10^scale`, as the float context selected:
/// its `of_decimal`, negated through its `neg` where it is written with a
/// `-`.
#[must_use]
pub fn decimal(digits: BigUint, scale: u32, negative: bool, float: &Float) -> LiteralExpr {
    let value = LiteralExpr::Call(
        float.of_decimal,
        vec![
            LiteralExpr::Natural(digits),
            LiteralExpr::Natural(BigUint::from(scale)),
        ],
    );
    if negative {
        LiteralExpr::Call(float.neg, vec![value])
    } else {
        value
    }
}

/// Elaborate a numeral after context has selected `Nat` or `Int`.
///
/// # Errors
///
/// Rejects a negative `Nat`; callers cannot accidentally erase its sign.
pub fn numeral(
    magnitude: BigUint,
    negative: bool,
    ty: NumeralType<'_>,
    prelude: &PreludeIds,
) -> Result<LiteralExpr, LiteralElaborationError> {
    if let NumeralType::Word(word) = ty {
        // What may be written, not what may be computed: `of_nat` wraps,
        // and a numeral that would wrap is refused.
        if negative {
            return Err(LiteralElaborationError::Negative(word.name.clone()));
        }
        if magnitude >= word.below {
            return Err(LiteralElaborationError::TooLarge {
                written: magnitude,
                name: word.name.clone(),
                below: word.below.clone(),
            });
        }
        return Ok(LiteralExpr::Call(
            word.of_nat,
            vec![LiteralExpr::Natural(magnitude)],
        ));
    }
    let natural = LiteralExpr::Natural(magnitude);
    match (ty, negative) {
        (NumeralType::Nat, false) => Ok(natural),
        (NumeralType::Nat, true) => Err(LiteralElaborationError::NegativeNat),
        (NumeralType::Int, false) => Ok(LiteralExpr::Call(prelude.int_of_nat, vec![natural])),
        (NumeralType::Int, true) => Ok(LiteralExpr::Call(
            prelude.int_neg,
            vec![LiteralExpr::Call(prelude.int_of_nat, vec![natural])],
        )),
        (NumeralType::Word(_), _) => unreachable!("a word is elaborated above"),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralElaborationError {
    NegativeNat,
    /// A word has no negative numerals.
    Negative(String),
    /// A numeral a word's `of_nat` would wrap.
    TooLarge {
        written: BigUint,
        name: String,
        below: BigUint,
    },
}

impl fmt::Display for LiteralElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NegativeNat => f.write_str("a negative numeral cannot be a Nat"),
            Self::Negative(name) => write!(f, "a `{name}` has no negative numerals"),
            Self::TooLarge {
                written,
                name,
                below,
            } => write!(
                f,
                "`{written}` is not a `{name}`: it takes numerals below {below}"
            ),
        }
    }
}

impl std::error::Error for LiteralElaborationError {}

/// Build a `Str` directly from valid UTF-8 bytes using its private wrappers.
#[must_use]
pub fn string(bytes: &[u8], prelude: &PreludeIds) -> LiteralExpr {
    let mut list = LiteralExpr::Construct(prelude.list_nil, Vec::new());
    for &byte in bytes.iter().rev() {
        let byte = LiteralExpr::Construct(
            prelude.u8_constructor,
            vec![LiteralExpr::Natural(BigUint::from(byte))],
        );
        list = LiteralExpr::Construct(prelude.list_cons, vec![byte, list]);
    }
    LiteralExpr::Construct(prelude.str_constructor, vec![list])
}

/// The word the prelude exports as `name`, where it has an `of_nat` and its
/// module declares `numerals_below` as a numeral.
fn word(program: &LoadedProgram, name: &str) -> Option<Word> {
    let binding = binding(program, name).ok()?;
    let of_nat = method(program, &binding, name, "of_nat").ok()?;
    let equals = method(program, &binding, name, "equals").ok()?;
    let local = symbol(&program.symbols, name).ok()?;
    let module = program.modules.iter().find(|module| {
        module
            .scope
            .types
            .get(&local)
            .is_some_and(|found| found.canonical == binding.canonical)
            && module.syntax.items.iter().any(|item| {
                matches!(item, crate::ast::Item::Data(data)
                if program.sources.get(module.source).is_some_and(|source| {
                    data.name.text(source.text()) == name
                }))
            })
    })?;
    let source = program.sources.get(module.source)?.text();
    let below = module.syntax.items.iter().find_map(|item| match item {
        crate::ast::Item::Clause(clause)
            if clause.name.text(source) == "numerals_below" && clause.body.bindings.is_empty() =>
        {
            match clause.body.result.kind {
                crate::ast::ExprKind::Number(numeral) => {
                    crate::literal::magnitude(numeral, source).ok()
                }
                _ => None,
            }
        }
        _ => None,
    })?;
    Some(Word {
        ty: binding.canonical,
        name: name.to_owned(),
        of_nat,
        equals,
        below,
    })
}

fn binding(program: &LoadedProgram, name: &str) -> Result<TypeBinding, PreludeError> {
    let local = symbol(&program.symbols, name)?;
    program
        .module(program.prelude)
        .public
        .types
        .get(&local)
        .cloned()
        .ok_or_else(|| PreludeError {
            message: format!("the prelude does not export type `{name}`"),
        })
}

fn binding_with_private_constructor(
    program: &LoadedProgram,
    name: &str,
) -> Result<TypeBinding, PreludeError> {
    let public = binding(program, name)?;
    let local = symbol(&program.symbols, name)?;
    program
        .modules
        .iter()
        .filter_map(|module| module.scope.types.get(&local))
        .find(|binding| {
            binding.canonical == public.canonical && binding.constructors.contains_key(&local)
        })
        .cloned()
        .ok_or_else(|| PreludeError {
            message: format!("standard type `{name}` has no private wrapper constructor `{name}`"),
        })
}

fn method(
    program: &LoadedProgram,
    binding: &TypeBinding,
    owner: &str,
    name: &str,
) -> Result<Symbol, PreludeError> {
    let local = symbol(&program.symbols, name)?;
    binding
        .methods
        .get(&local)
        .copied()
        .ok_or_else(|| PreludeError {
            message: format!("standard type `{owner}` has no method `{name}`"),
        })
}

fn constructor(
    program: &LoadedProgram,
    binding: &TypeBinding,
    owner: &str,
    name: &str,
) -> Result<Symbol, PreludeError> {
    let local = symbol(&program.symbols, name)?;
    binding
        .constructors
        .get(&local)
        .copied()
        .ok_or_else(|| PreludeError {
            message: format!("standard type `{owner}` has no constructor `{name}`"),
        })
}

fn symbol(symbols: &Symbols, name: &str) -> Result<Symbol, PreludeError> {
    symbols.find(name).ok_or_else(|| PreludeError {
        message: format!("standard name `{name}` was never declared"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let root = std::env::temp_dir().join(format!("faun-blessed-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn loaded() -> LoadedProgram {
        let fixture = Fixture::new();
        fixture.write("bool.fn", "exports {Bool.*}\nBool : [False, True].(not : Bool -> Bool\nnot(False) -> True\nnot(True) -> False\nand : (Bool, Bool) -> Bool\nand(True, True) -> True\nand(_, _) -> False)\n");
        fixture.write("nat.fn", "exports {Nat.*}\nNat : [Zero, Succ(Nat)]\n");
        fixture.write(
            "int.fn",
            "exports {Int.*}\nInt : [Pos(Nat), NegSucc(Nat)].(of_nat : Nat -> Int\nof_nat(n) -> Pos(n)\nneg : Int -> Int\nneg(i) -> i)\n",
        );
        fixture.write("u8.fn", "exports {U8}\nU8 : Nat\n");
        fixture.write(
            "list.fn",
            "exports {List.*}\nList(a) : [Nil, Cons(a, List(a))]\n",
        );
        fixture.write(
            "str.fn",
            "exports {Str}\nStr : List(U8).(concat : (Str, Str) -> Str\nconcat(left, _) -> left\nequals : (Str, Str) -> Bool\nequals(_, _) -> False)\n",
        );
        fixture.write(
            "result.fn",
            "exports {Result.*}\nResult(a, e) : [Ok(a), Err(e)]\n",
        );
        fixture.write(
            "order.fn",
            "exports {Order.*}\nOrder : [Lt, Eq, Gt].(lt : Order -> Bool\nlt(Lt) -> True\nlt(_) -> False\nle : Order -> Bool\nle(Gt) -> False\nle(_) -> True\ngt : Order -> Bool\ngt(Gt) -> True\ngt(_) -> False\nge : Order -> Bool\nge(Lt) -> False\nge(_) -> True\nthen : (Order, Order) -> Order\nthen(Eq, next) -> next\nthen(decided, _) -> decided)\n",
        );
        let root = fixture.write(
            "standard.fn",
            "package {}\nimport bool {Bool.*}\nimport order {Order.*}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport result {Result.*}\nimport str {Str}\nexports {Bool.*, Order.*, Nat.*, Int.*, U8, List.*, Result.*, Str}\n",
        );
        let entry = fixture.write("main.fn", "id(x) -> x\n");
        // The loader owns all source text, so removing the fixture afterwards
        // does not invalidate the program.
        let host = fixture.write("host.fn", "exports {Host}\nHost : {argc: Nat}\n");
        modules::load_program(&entry, &root, &host).unwrap()
    }

    #[test]
    fn int_numerals_use_library_conversions() {
        let loaded = loaded();
        let ids = PreludeIds::find_in(&loaded).unwrap();
        assert_eq!(
            numeral(BigUint::from(42u8), true, NumeralType::Int, &ids).unwrap(),
            LiteralExpr::Call(
                ids.int_neg,
                vec![LiteralExpr::Call(
                    ids.int_of_nat,
                    vec![LiteralExpr::Natural(BigUint::from(42u8))]
                )]
            )
        );
        assert_eq!(
            numeral(BigUint::from(42u8), false, NumeralType::Nat, &ids).unwrap(),
            LiteralExpr::Natural(BigUint::from(42u8))
        );
        assert_eq!(
            numeral(BigUint::from(1u8), true, NumeralType::Nat, &ids),
            Err(LiteralElaborationError::NegativeNat)
        );
    }

    #[test]
    fn strings_use_private_utf8_cells() {
        let loaded = loaded();
        let ids = PreludeIds::find_in(&loaded).unwrap();
        let value = string("é".as_bytes(), &ids);
        let LiteralExpr::Construct(str_constructor, outer) = value else {
            panic!("Str wrapper")
        };
        assert_eq!(str_constructor, ids.str_constructor);
        let LiteralExpr::Construct(first_cons, _) = &outer[0] else {
            panic!("first byte cell")
        };
        assert_eq!(*first_cons, ids.list_cons);
    }
}
