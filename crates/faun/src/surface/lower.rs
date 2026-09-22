//! Lower elaborated literals into Barb terms.
//!
//! General HIR lowering will eventually own declaration translation. This
//! narrow boundary already proves that blessed literal expansion uses ordinary
//! Barb constants, constructors, and calls rather than backend intrinsics.

use std::collections::HashMap;
use std::fmt;

use crate::barb::{Atom, Builder, ConstructionError, CtorId, FnId, TypeId};

use super::Symbol;
use super::blessed::LiteralExpr;

#[derive(Clone, Debug)]
pub struct LiteralDeclarations {
    pub nat: TypeId,
    constructors: HashMap<Symbol, CtorId>,
    functions: HashMap<Symbol, FnId>,
}

impl LiteralDeclarations {
    #[must_use]
    pub fn new(nat: TypeId) -> Self {
        Self {
            nat,
            constructors: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    pub fn constructor(&mut self, surface: Symbol, barb: CtorId) {
        self.constructors.insert(surface, barb);
    }

    pub fn function(&mut self, surface: Symbol, barb: FnId) {
        self.functions.insert(surface, barb);
    }

    /// Lower one fully elaborated literal expression.
    ///
    /// Missing declaration mappings are checked before terms are emitted.
    /// A malformed Barb natural type can still fail after earlier subterms have
    /// been appended; the enclosing function must then be discarded rather
    /// than defined from that builder.
    ///
    /// # Errors
    ///
    /// Reports a missing declaration mapping or a Barb constant-construction
    /// failure.
    pub fn lower(
        &self,
        builder: &mut Builder<'_>,
        expression: &LiteralExpr,
    ) -> Result<Atom, LiteralLowerError> {
        self.validate(expression)?;
        self.emit(builder, expression)
    }

    fn validate(&self, expression: &LiteralExpr) -> Result<(), LiteralLowerError> {
        match expression {
            LiteralExpr::Natural(_) => Ok(()),
            LiteralExpr::Construct(constructor, fields) => {
                if !self.constructors.contains_key(constructor) {
                    return Err(LiteralLowerError::MissingConstructor(*constructor));
                }
                fields.iter().try_for_each(|field| self.validate(field))
            }
            LiteralExpr::Call(function, arguments) => {
                if !self.functions.contains_key(function) {
                    return Err(LiteralLowerError::MissingFunction(*function));
                }
                arguments
                    .iter()
                    .try_for_each(|argument| self.validate(argument))
            }
        }
    }

    fn emit(
        &self,
        builder: &mut Builder<'_>,
        expression: &LiteralExpr,
    ) -> Result<Atom, LiteralLowerError> {
        match expression {
            LiteralExpr::Natural(magnitude) => {
                let constant = builder.natural(self.nat, magnitude)?;
                Ok(builder.known(constant))
            }
            LiteralExpr::Construct(constructor, fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.emit(builder, field))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(builder.con(self.constructors[constructor], &fields))
            }
            LiteralExpr::Call(function, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.emit(builder, argument))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(builder.call(self.functions[function], &arguments))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralLowerError {
    MissingConstructor(Symbol),
    MissingFunction(Symbol),
    Constant(ConstructionError),
}

impl From<ConstructionError> for LiteralLowerError {
    fn from(error: ConstructionError) -> Self {
        Self::Constant(error)
    }
}

impl fmt::Display for LiteralLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingConstructor(symbol) => {
                write!(
                    f,
                    "no Barb constructor mapped for surface symbol {symbol:?}"
                )
            }
            Self::MissingFunction(symbol) => {
                write!(f, "no Barb function mapped for surface symbol {symbol:?}")
            }
            Self::Constant(error) => fmt::Display::fmt(error, f),
        }
    }
}

impl std::error::Error for LiteralLowerError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::barb;
    use crate::surface::Symbols;
    use num_bigint::BigUint;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn literal_expansion_is_ordinary_valid_barb() {
        let mut names = Symbols::default();
        let surface_str = names.intern("Str$$Str");
        let surface_u8 = names.intern("U8$$U8");
        let surface_nil = names.intern("List$$Nil");
        let surface_cons = names.intern("List$$Cons");
        let surface_of_nat = names.intern("Int.of_nat");
        let surface_neg = names.intern("Int.neg");

        let mut program = barb::Program::default();
        let nat = program.declare_type("Nat");
        let int = program.declare_type("Int");
        let u8_ = program.declare_type("U8");
        let list = program.declare_type("ListU8");
        let str_ = program.declare_type("Str");
        program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        program.define_type(int, &[("Pos", &[nat]), ("NegSucc", &[nat])]);
        program.define_type(u8_, &[("U8", &[nat])]);
        program.define_type(list, &[("Nil", &[]), ("Cons", &[u8_, list])]);
        program.define_type(str_, &[("Str", &[list])]);

        let mut declarations = LiteralDeclarations::new(nat);
        declarations.constructor(surface_str, program.ctor_at(str_, 0));
        declarations.constructor(surface_u8, program.ctor_at(u8_, 0));
        declarations.constructor(surface_nil, program.ctor_at(list, 0));
        declarations.constructor(surface_cons, program.ctor_at(list, 1));
        let of_nat = program.declare("Int.of_nat", &[nat], int);
        let neg = program.declare("Int.neg", &[int], int);
        declarations.function(surface_of_nat, of_nat);
        declarations.function(surface_neg, neg);

        let literal = LiteralExpr::Construct(
            surface_str,
            vec![LiteralExpr::Construct(
                surface_cons,
                vec![
                    LiteralExpr::Construct(
                        surface_u8,
                        vec![LiteralExpr::Natural(BigUint::from(65u8))],
                    ),
                    LiteralExpr::Construct(surface_nil, Vec::new()),
                ],
            )],
        );
        let function = program.declare("text", &[], str_);
        program.define(function, |builder, _| {
            declarations.lower(builder, &literal).unwrap()
        });
        let integer = LiteralExpr::Call(
            surface_neg,
            vec![LiteralExpr::Call(
                surface_of_nat,
                vec![LiteralExpr::Natural(BigUint::from(42u8))],
            )],
        );
        let entry = program.declare("integer", &[], int);
        program.define(entry, |builder, _| {
            declarations.lower(builder, &integer).unwrap()
        });
        program.set_entry(entry);
        barb::validate(&program).unwrap();
    }
}
