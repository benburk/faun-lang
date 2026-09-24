//! Terms, declarations, and their IDs.
//!
//! [`super::Program`] owns the pools these values refer to.

pub use crate::index::Range;
use crate::index::index;

// `Symbol` is a name. Most IR passes do not read the characters of one: names are
// compared, hashed and copied as integers, and the string is read back only
// to render it. The table belongs to the program, like every other pool
// here, so a program is a self-contained value and two of them cannot
// disagree about what a symbol means.
index!(ExprId, FnId, TypeId, CtorId, ConstId, Local, Symbol);

/// An argument: a local, and nothing else. That is what A-normal form buys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Atom(pub Local);

/// A term.
///
/// Binders are implicit. Locals are de Bruijn levels: a function's parameters
/// are the first of them, each [`Body`] binding binds the next, and an [`Arm`] binds
/// its constructor's fields in order. Two sibling arms reuse the same levels
/// because they are alternative paths, so a term carries no names and two
/// structurally equal terms are equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expr {
    /// A bare atom.
    Atom(Atom),
    /// A saturated constructor application.
    Con(CtorId, Range),
    /// A value known outright, held encoded rather than as a chain of `Con`.
    Static(ConstId),
    /// A saturated call to a top-level name. Every recursive edge is one.
    Call(FnId, Range),
    /// Destructuring. An arm per constructor of the scrutinee's type.
    Match(Atom, Range),
}

/// A run of bindings and the expression they are for. Each binding takes the
/// next local, in order, and the tail answers the body's value.
///
/// This is the shape of [`crate::ir::Region`] one tier down, so that lowering
/// a body is a scan rather than a change of shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Body {
    pub bindings: Range,
    pub tail: ExprId,
}

/// One branch of a match. Binds its constructor's fields as the next locals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Arm {
    pub ctor: CtorId,
    pub body: Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Type {
    pub name: Symbol,
    /// Whether diagnostic rendering writes this type at each use rather than
    /// as a separate declaration.
    pub(super) inline: bool,
    pub(super) definition: TypeDefinition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TypeDefinition {
    Declared,
    Defined(Range),
}

impl Type {
    /// Return whether diagnostic rendering omits a separate declaration.
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.inline
    }

    /// Constructors are assigned once, including an empty run for an empty type.
    ///
    /// # Panics
    /// If the declaration has not yet been defined.
    #[must_use]
    pub fn constructors(&self) -> Range {
        match self.definition {
            TypeDefinition::Defined(ctors) => ctors,
            TypeDefinition::Declared => panic!("a type must be defined before use"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctor {
    pub name: Symbol,
    pub owner: TypeId,
    /// The types of its fields, in order.
    pub fields: Range,
    /// Each field's name and declared bounds, parallel to `fields`.
    pub details: Range,
}

/// What a constructor's field is called, as its declaration said.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct FieldDetail {
    pub name: Option<Symbol>,
}

/// One field of a constructor, as a type definition gives it: its type, and
/// optionally the name it is read by. A name is for reading: a program
/// printed, and a tier below naming what it holds.
#[derive(Clone, Copy, Debug)]
pub struct Field<'a> {
    pub ty: TypeId,
    pub name: Option<&'a str>,
}

impl<'a> Field<'a> {
    /// A field of type `ty`, unnamed.
    #[must_use]
    pub const fn of(ty: TypeId) -> Self {
        Self { ty, name: None }
    }

    #[must_use]
    pub const fn named(self, name: &'a str) -> Self {
        Self {
            name: Some(name),
            ..self
        }
    }
}

/// A body or a host declaration, never both. External calls are observable:
/// optimization may not discard, duplicate or reorder them. Defined functions
/// may themselves call external routines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Definition {
    Body(Body),
    External {
        /// Provider name, which may differ from the source name.
        symbol: Symbol,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Parameter {
    pub name: Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// Diagnostic name; frontend declarations preserve the source spelling.
    /// External linkage uses the symbol in `definition`, not this name.
    pub name: Symbol,
    /// The types of its parameters, which are the first locals.
    pub params: Range,
    /// Parameter names, parallel to `params`.
    pub(super) parameters: Range,
    pub result: TypeId,
    pub definition: Definition,
}

impl Function {
    #[must_use]
    pub const fn body(&self) -> Option<Body> {
        match self.definition {
            Definition::Body(body) => Some(body),
            Definition::External { .. } => None,
        }
    }

    /// The name something outside answers a bodyless declaration by.
    #[must_use]
    pub const fn provider(&self) -> Option<Symbol> {
        match self.definition {
            Definition::External { symbol } => Some(symbol),
            Definition::Body(_) => None,
        }
    }

    pub(super) const fn define(&mut self, body: Body) {
        self.definition = Definition::Body(body);
    }
}
