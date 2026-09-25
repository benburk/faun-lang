//! Defunctionalize specialized terms, making every function value data.
//!
//! Each function type becomes a closure type whose constructors are the
//! closures of that type the program makes: a global function, a constructor
//! used as a function, or a lambda holding the locals it captures. Calling a
//! function value becomes a call to its type's `apply`, which matches on the
//! closure and does what it stands for. What remains is first order: an
//! expression makes a function value only by naming a closure, and calls one
//! only through `apply`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use num_bigint::BigUint;

use crate::hir::{self as h, LocalId};
use crate::specialize::{self, FunctionKey, Pattern, Type};
use crate::{ModuleId, Symbol};

/// A specialized program with no function values but closures.
#[derive(Clone, Debug)]
pub(crate) struct Program {
    /// Where the program starts, when it is an application.
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    /// For each function type, the closures a value of it may be, in the
    /// order they were found.
    pub(crate) closures: BTreeMap<Type, Vec<Closure>>,
    /// The function types some expression applies, each needing an `apply`.
    pub(crate) applied: BTreeSet<Type>,
    pub(crate) data: HashMap<Symbol, h::DataDecl>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) clauses: Vec<Clause>,
    pub(crate) provider: Option<Symbol>,
}

#[derive(Clone, Debug)]
pub(crate) struct Clause {
    pub(crate) patterns: Vec<Pattern>,
    pub(crate) guard: Option<Expr>,
    pub(crate) body: Body,
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) bindings: Vec<Binding>,
    pub(crate) result: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub(crate) pattern: Pattern,
    pub(crate) value: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Expr {
    /// Where it was written, which a diagnostic about it points at.
    pub(crate) module: ModuleId,
    pub(crate) span: crate::ast::Span,
    pub(crate) ty: Type,
    pub(crate) kind: ExprKind,
}

#[derive(Clone, Debug)]
pub(crate) enum ExprKind {
    Local(LocalId),
    Natural(BigUint),
    Construct(Symbol, Vec<Expr>),
    Record(Vec<(Symbol, Expr)>),
    Project(Box<Expr>, Symbol),
    DirectCall(FunctionKey, Vec<Expr>),
    /// The closure named by the key, holding these locals' values in the
    /// order of its captures. The expression's type is the function type it
    /// is a closure of.
    Close(ClosureKey, Vec<LocalId>),
    /// Apply the closure the head makes through `apply` for its type.
    Apply(Box<Expr>, Vec<Expr>),
}

/// Which closure of a function type: what it does when applied.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ClosureKey {
    /// Call a global function with the arguments.
    Global(FunctionKey),
    /// Build a value of the function type's result with a constructor.
    Constructor(Symbol, Type),
    /// Run the lambda written at this place.
    Lambda(ModuleId, crate::ast::Span, Type),
}

#[derive(Clone, Debug)]
pub(crate) struct Closure {
    pub(crate) key: ClosureKey,
    /// The locals a lambda reads from where it was written, in order.
    pub(crate) captures: Vec<(LocalId, Type)>,
    /// A lambda's parameter patterns and body, which read its captures and
    /// parameters. Present exactly when the key is a lambda.
    pub(crate) lambda: Option<(Vec<Pattern>, Expr)>,
}

/// Replace every function value in `program` with a closure.
pub(crate) fn defunctionalize(program: specialize::Program) -> Program {
    let mut pass = Defunctionalizer::default();
    let functions = program
        .functions
        .into_iter()
        .map(|function| pass.function(function))
        .collect();
    Program {
        entry: program.entry,
        functions,
        closures: pass.closures,
        applied: pass.applied,
        data: program.data,
    }
}

#[derive(Default)]
struct Defunctionalizer {
    closures: BTreeMap<Type, Vec<Closure>>,
    applied: BTreeSet<Type>,
}

impl Defunctionalizer {
    fn function(&mut self, function: specialize::Function) -> Function {
        let clauses = function
            .clauses
            .into_iter()
            .map(|clause| Clause {
                patterns: clause.patterns,
                guard: clause.guard.map(|guard| self.expr(guard)),
                body: self.body(clause.body),
            })
            .collect();
        Function {
            key: function.key,
            clauses,
            provider: function.provider,
        }
    }

    fn body(&mut self, body: specialize::Body) -> Body {
        let bindings = body
            .bindings
            .into_iter()
            .map(|binding| Binding {
                pattern: binding.pattern,
                value: self.expr(binding.value),
            })
            .collect();
        Body {
            bindings,
            result: self.expr(body.result),
        }
    }

    fn exprs(&mut self, expressions: Vec<specialize::Expr>) -> Vec<Expr> {
        expressions
            .into_iter()
            .map(|expression| self.expr(expression))
            .collect()
    }

    fn expr(&mut self, expression: specialize::Expr) -> Expr {
        use specialize::ExprKind as S;
        let (module, span, ty) = (expression.module, expression.span, expression.ty);
        let kind = match expression.kind {
            S::Local(local) => ExprKind::Local(local),
            S::Natural(magnitude) => ExprKind::Natural(magnitude),
            S::Construct(constructor, fields) => {
                ExprKind::Construct(constructor, self.exprs(fields))
            }
            S::Record(fields) => ExprKind::Record(
                fields
                    .into_iter()
                    .map(|(name, field)| (name, self.expr(field)))
                    .collect(),
            ),
            S::Project(receiver, field) => ExprKind::Project(Box::new(self.expr(*receiver)), field),
            S::DirectCall(key, arguments) => ExprKind::DirectCall(key, self.exprs(arguments)),
            S::Function(key) => self.close(&ty, ClosureKey::Global(key), Vec::new()),
            S::ConstructorFunction(constructor) => self.close(
                &ty,
                ClosureKey::Constructor(constructor, ty.clone()),
                Vec::new(),
            ),
            S::Lambda(patterns, body) => {
                let key = ClosureKey::Lambda(module, span, ty.clone());
                self.lambda(&ty, &key, patterns, *body)
            }
            S::Invoke(head, arguments) => {
                self.applied.insert(head.ty.clone());
                let head = self.expr(*head);
                ExprKind::Apply(Box::new(head), self.exprs(arguments))
            }
        };
        Expr {
            module,
            span,
            ty,
            kind,
        }
    }

    /// Record a lambda as a closure of `ty`, with its body made first order.
    fn lambda(
        &mut self,
        ty: &Type,
        key: &ClosureKey,
        patterns: Vec<Pattern>,
        body: specialize::Expr,
    ) -> ExprKind {
        let close = self.close(ty, key.clone(), captures(&patterns, &body));
        let body = self.expr(body);
        if let Some(closure) = self
            .closures
            .get_mut(ty)
            .and_then(|closures| closures.iter_mut().find(|closure| closure.key == *key))
            .filter(|closure| closure.lambda.is_none())
        {
            closure.lambda = Some((patterns, body));
        }
        close
    }

    /// Record the closure `key` of `ty`, once, and make it from its captures.
    fn close(&mut self, ty: &Type, key: ClosureKey, captures: Vec<(LocalId, Type)>) -> ExprKind {
        let locals = captures.iter().map(|(local, _)| *local).collect();
        let closures = self.closures.entry(ty.clone()).or_default();
        if !closures.iter().any(|held| held.key == key) {
            closures.push(Closure {
                key: key.clone(),
                captures,
                lambda: None,
            });
        }
        ExprKind::Close(key, locals)
    }
}

/// The locals a lambda's body reads that its parameters do not bind.
fn captures(patterns: &[Pattern], body: &specialize::Expr) -> Vec<(LocalId, Type)> {
    let mut bound = HashSet::new();
    for pattern in patterns {
        pattern_locals(pattern, &mut bound);
    }
    let mut found = BTreeMap::new();
    free_locals(body, &bound, &mut found);
    found.into_iter().collect()
}

fn free_locals(
    expression: &specialize::Expr,
    bound: &HashSet<LocalId>,
    found: &mut BTreeMap<LocalId, Type>,
) {
    use specialize::ExprKind as S;
    match &expression.kind {
        S::Local(local) => {
            if !bound.contains(local) {
                found.entry(*local).or_insert_with(|| expression.ty.clone());
            }
        }
        S::Function(_) | S::ConstructorFunction(_) | S::Natural(_) => {}
        S::Construct(_, fields) | S::DirectCall(_, fields) => {
            for field in fields {
                free_locals(field, bound, found);
            }
        }
        S::Record(fields) => {
            for (_, field) in fields {
                free_locals(field, bound, found);
            }
        }
        S::Project(receiver, _) => free_locals(receiver, bound, found),
        S::Invoke(head, arguments) => {
            free_locals(head, bound, found);
            for argument in arguments {
                free_locals(argument, bound, found);
            }
        }
        S::Lambda(patterns, body) => {
            let mut nested = bound.clone();
            for pattern in patterns {
                pattern_locals(pattern, &mut nested);
            }
            free_locals(body, &nested, found);
        }
    }
}

fn pattern_locals(pattern: &Pattern, output: &mut HashSet<LocalId>) {
    match pattern {
        Pattern::Bind(local) => {
            output.insert(*local);
        }
        Pattern::Constructor(_, fields)
        | Pattern::List(fields, None)
        | Pattern::Product(fields) => {
            for field in fields {
                pattern_locals(field, output);
            }
        }
        Pattern::List(fields, Some(rest)) => {
            for field in fields {
                pattern_locals(field, output);
            }
            pattern_locals(rest, output);
        }
        Pattern::Record(fields) => {
            for (_, pattern) in fields {
                pattern_locals(pattern, output);
            }
        }
        Pattern::Wild | Pattern::Number { .. } | Pattern::Range(_, _) => {}
    }
}
