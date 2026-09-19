//! Terms, declarations, and their IDs.
//!
//! [`super::Program`] owns the pools these values refer to.

pub use crate::index::Range;
use crate::index::index;

// `Symbol` is a name. The IR never reads the characters of one: names are
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
    Static(TypeId, ConstId),
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
    pub ctors: Range,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctor {
    pub name: Symbol,
    pub owner: TypeId,
    /// The types of its fields, in order.
    pub fields: Range,
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
        /// An optional range contract for a natural-valued result.
        bounds: Option<super::Bounds>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: Symbol,
    /// The types of its parameters, which are the first locals.
    pub params: Range,
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

    #[must_use]
    pub const fn bounds(&self) -> Option<super::Bounds> {
        match self.definition {
            Definition::External { bounds, .. } => bounds,
            Definition::Body(_) => None,
        }
    }

    pub(super) const fn define(&mut self, body: Body) {
        self.definition = Definition::Body(body);
    }
}
