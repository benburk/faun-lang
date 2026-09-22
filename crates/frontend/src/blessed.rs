//! The small syntax-to-prelude contract for literals.
//!
//! These are not runtime intrinsics. Numerals remain ordinary `Nat` values;
//! an `Int` literal calls the library's `of_nat` and optional `neg`, while a
//! string literal is permitted to construct the private `Str`/`List`/`U8`
//! representation. Canonical identities are discovered once from the loaded
//! standard package instead of compared by spelling throughout later passes.

use std::fmt;

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
    pub u8_constructor: Symbol,
    pub list_nil: Symbol,
    pub list_cons: Symbol,
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
    pub fn resolve(program: &LoadedProgram) -> Result<Self, PreludeError> {
        let bool_ = binding(program, "Bool")?;
        let nat = binding(program, "Nat")?;
        let int = binding(program, "Int")?;
        let str_ = binding_with_private_constructor(program, "Str")?;
        let u8_ = binding_with_private_constructor(program, "U8")?;
        let list = binding(program, "List")?;
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
            u8_constructor: constructor(program, &u8_, "U8", "U8")?,
            list_nil: constructor(program, &list, "List", "Nil")?,
            list_cons: constructor(program, &list, "List", "Cons")?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumeralType {
    Nat,
    Int,
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

/// Elaborate a numeral after context has selected `Nat` or `Int`.
///
/// # Errors
///
/// Rejects a negative `Nat`; callers cannot accidentally erase its sign.
pub fn numeral(
    magnitude: BigUint,
    negative: bool,
    ty: NumeralType,
    prelude: &PreludeIds,
) -> Result<LiteralExpr, LiteralElaborationError> {
    let natural = LiteralExpr::Natural(magnitude);
    match (ty, negative) {
        (NumeralType::Nat, false) => Ok(natural),
        (NumeralType::Nat, true) => Err(LiteralElaborationError::NegativeNat),
        (NumeralType::Int, false) => Ok(LiteralExpr::Call(prelude.int_of_nat, vec![natural])),
        (NumeralType::Int, true) => Ok(LiteralExpr::Call(
            prelude.int_neg,
            vec![LiteralExpr::Call(prelude.int_of_nat, vec![natural])],
        )),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralElaborationError {
    NegativeNat,
}

impl fmt::Display for LiteralElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NegativeNat => f.write_str("a negative numeral cannot be a Nat"),
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

fn binding(program: &LoadedProgram, name: &str) -> Result<TypeBinding, PreludeError> {
    let local = symbol(&program.symbols, name)?;
    let prelude = program.prelude.ok_or_else(|| PreludeError {
        message: "literal syntax needs a loaded prelude".to_string(),
    })?;
    program
        .module(prelude)
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
        fixture.write("bool.fn", "exports {Bool.*}\nBool : [False True].(not : Bool -> Bool not(False) -> True not(True) -> False)\n");
        fixture.write("nat.fn", "exports {Nat.*}\nNat : [Zero Succ(Nat)]\n");
        fixture.write(
            "int.fn",
            "exports {Int.*}\nInt : [Pos(Nat) NegSucc(Nat)].(of_nat : Nat -> Int of_nat(n) -> Pos(n) neg : Int -> Int neg(i) -> i)\n",
        );
        fixture.write("u8.fn", "exports {U8}\nU8 : Nat\n");
        fixture.write(
            "list.fn",
            "exports {List.*}\nList(a) : [Nil Cons(a List(a))]\n",
        );
        fixture.write("str.fn", "exports {Str}\nStr : List(U8)\n");
        let root = fixture.write(
            "standard.fn",
            "lib {}\nimport bool {Bool.*}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport str {Str}\nexports {Bool.* Nat.* Int.* U8 List.* Str}\n",
        );
        let entry = fixture.write("main.fn", "id(x) -> x\n");
        // The loader owns all source text, so removing the fixture afterwards
        // does not invalidate the program.
        modules::load(&[entry], Some(&root)).unwrap()
    }

    #[test]
    fn int_numerals_use_library_conversions() {
        let loaded = loaded();
        let ids = PreludeIds::resolve(&loaded).unwrap();
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
        let ids = PreludeIds::resolve(&loaded).unwrap();
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
