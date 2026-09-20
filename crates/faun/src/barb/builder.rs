//! Scoped construction of function bodies.
//!
//! [`Program::define`] starts construction; this module owns the temporary
//! bindings and local levels used to build a body.
//!
//! Every operation returns an [`Atom`], and the `Let` that binds it is
//! written for you: A-normal form is the shape of the IR, not a burden on
//! whoever constructs it. A caller never names a local and never sees an
//! [`ExprId`].

use super::ConstructionError;
use super::model::{Arm, Atom, Body, ConstId, CtorId, Expr, ExprId, FnId, Local, TypeId};
use super::program::Program;

/// Builds one function's body.
///
/// Bindings accumulate in order and become a `Body` when the scope
/// closes, which is what lets an operation hand back an atom. Locals are de
/// Bruijn levels, so the level a binding takes is fixed the moment it is
/// emitted and no renaming is ever needed.
#[derive(Debug)]
pub struct Builder<'a> {
    program: &'a mut Program,
    pending: Vec<ExprId>,
    level: u32,
}

impl Builder<'_> {
    /// Build a root scope with the function's parameters as its first locals.
    pub(super) fn build(
        program: &mut Program,
        arity: u32,
        build: impl FnOnce(&mut Builder, &[Atom]) -> Atom,
    ) -> Body {
        let mut builder = Builder {
            program,
            pending: Vec::new(),
            level: 0,
        };
        builder.scope(arity, build)
    }

    /// A saturated constructor application.
    pub fn con(&mut self, ctor: CtorId, args: &[Atom]) -> Atom {
        let args = self.program.terms.hold_atoms(args.iter().copied());
        self.emit(Expr::Con(ctor, args))
    }

    /// A saturated call to a top-level name.
    pub fn call(&mut self, function: FnId, args: &[Atom]) -> Atom {
        let args = self.program.terms.hold_atoms(args.iter().copied());
        self.emit(Expr::Call(function, args))
    }

    /// Hold a number in the program's pool, for [`Self::known`].
    ///
    /// # Errors
    /// If the type is undefined or is not a natural-number shape.
    pub fn number(&mut self, id: TypeId, value: u64) -> Result<ConstId, ConstructionError> {
        self.program.intern_number(id, value)
    }

    /// A value known outright.
    pub fn known(&mut self, value: ConstId) -> Atom {
        self.emit(Expr::Static(value))
    }

    /// One arm per constructor of `owner`, in tag order, so a match is
    /// exhaustive by construction. Each arm binds its constructor's fields
    /// as the next locals; sibling arms take the same ones, being
    /// alternatives rather than a sequence.
    ///
    /// # Panics
    ///
    /// If the type outgrew the constructors it may have.
    pub fn match_(
        &mut self,
        scrutinee: Atom,
        owner: TypeId,
        mut arm: impl FnMut(&mut Self, CtorId, &[Atom]) -> Atom,
    ) -> Atom {
        let count =
            u32::try_from(self.program.ctors(owner).len()).expect("a sane constructor count");
        let mut arms =
            Vec::with_capacity(usize::try_from(count).expect("a count that fits a pointer"));
        for tag in 0..count {
            let ctor = self.program.ctor_at(owner, tag);
            let fields =
                u32::try_from(self.program.fields(ctor).len()).expect("a sane constructor arity");
            let body = self.scope(fields, |builder, bound| arm(builder, ctor, bound));
            arms.push(Arm { ctor, body });
        }
        let arms = self.program.terms.hold_arms(&arms);
        self.emit(Expr::Match(scrutinee, arms))
    }

    /// Bind an expression to the next local and answer it.
    fn emit(&mut self, expr: Expr) -> Atom {
        let id = self.program.terms.push(expr);
        self.pending.push(id);
        let bound = Atom(Local(self.level));
        self.level += 1;
        bound
    }

    /// Build a nested scope that first binds `bound` locals of its own.
    fn scope(&mut self, bound: u32, build: impl FnOnce(&mut Self, &[Atom]) -> Atom) -> Body {
        let outer = std::mem::take(&mut self.pending);
        let level = self.level;
        let binders: Vec<Atom> = (0..bound).map(|at| Atom(Local(level + at))).collect();
        self.level = level + bound;

        let result = build(self, &binders);
        let body = self.close(result);

        self.pending = outer;
        self.level = level;
        body
    }

    /// This scope's bindings, with its result as the tail. A result that is
    /// the last binding becomes the tail itself rather than a binding an
    /// atom then reads back, since nothing after it could have read it.
    fn close(&mut self, result: Atom) -> Body {
        let mut pending = std::mem::take(&mut self.pending);
        let last = self.level.checked_sub(1).map(Local);
        let tail = match pending.pop() {
            Some(expr) if last == Some(result.0) => expr,
            Some(expr) => {
                pending.push(expr);
                self.program.terms.push(Expr::Atom(result))
            }
            None => self.program.terms.push(Expr::Atom(result)),
        };
        self.program.terms.hold_body(&pending, tail)
    }
}
