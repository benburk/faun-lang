//! The members a closed record, a tuple or a tag row has without anything
//! declaring them: `equals`, `cmp`, `to_str` and `hash_into`, each made at
//! the type specialization reached it at, from its components' own members.
//!
//! A declared type's members are written before checking instead, so they
//! are held to the signature and bounds written for them; see
//! [`crate::derive`]. Nothing is written for these, and what their
//! components are is known only here.

use super::{
    Body, Clause, Connective, Definition, Expr, ExprKind, Function, FunctionKey, Pattern,
    Specializer, Type, error,
};
use crate::diagnostic::Refusal;
use crate::hir as h;
use crate::{ModuleId, Symbol, Symbols};

/// Where the member was first asked for, which its parts are placed at.
type At = (ModuleId, crate::ast::Span);

/// One way a value of a structural type is built: a tag of a row, a tuple,
/// or a record, and the types of its components in the order it is taken
/// apart in.
struct Shape {
    kind: Kind,
    components: Vec<Type>,
}

enum Kind {
    Tag(Symbol),
    Tuple,
    /// Each component's field name.
    Record(Vec<Symbol>),
}

impl Shape {
    /// The ways a value of `ty` is built: one for each tag of a row.
    fn of(ty: &Type) -> Vec<Self> {
        match ty {
            Type::Variants(tags) => tags
                .iter()
                .map(|(label, fields)| Self {
                    kind: Kind::Tag(*label),
                    components: fields.clone(),
                })
                .collect(),
            Type::Tuple(members) => vec![Self {
                kind: Kind::Tuple,
                components: members.clone(),
            }],
            Type::Record(fields) => vec![Self {
                kind: Kind::Record(fields.iter().map(|(name, _)| *name).collect()),
                components: fields.iter().map(|(_, ty)| ty.clone()).collect(),
            }],
            _ => unreachable!("only records, tuples and rows have structural members"),
        }
    }

    /// The same, a record's fields in the order of their names, as Ori
    /// renders a record, whatever order it was written or held in.
    fn by_name(mut self, symbols: &Symbols) -> Self {
        if let Kind::Record(names) = &mut self.kind {
            let mut fields: Vec<_> = names.drain(..).zip(self.components.drain(..)).collect();
            fields.sort_by(|a, b| symbols.text(a.0).cmp(symbols.text(b.0)));
            (*names, self.components) = fields.into_iter().unzip();
        }
        self
    }

    /// The pattern taking it apart, its components bound to the locals
    /// from `first` on.
    fn pattern(&self, first: u32) -> Pattern {
        let count = u32::try_from(self.components.len()).expect("fewer than 2^32 components");
        let binds = (first..first + count)
            .map(|index| Pattern::Bind(h::LocalId(index)))
            .collect();
        match &self.kind {
            Kind::Tag(label) => Pattern::Constructor(*label, binds),
            Kind::Tuple => Pattern::Product(binds),
            Kind::Record(names) => Pattern::Record(names.iter().copied().zip(binds).collect()),
        }
    }
}

impl Specializer<'_> {
    /// Whether `name` on these parameters is a closed record's or a
    /// tuple's own `equals`, `cmp`, `to_str` or `hash_into`, or a tag row's
    /// own `equals` or `to_str`.
    pub(super) fn is_structural(&self, name: Symbol, parameters: &[Type]) -> bool {
        let name = Some(name);
        match parameters.first() {
            Some(Type::Record(_) | Type::Tuple(_)) => [
                self.prelude.equals,
                self.prelude.cmp,
                self.prelude.to_str,
                self.prelude.hash_into,
            ]
            .contains(&name),
            Some(Type::Variants(_)) => [self.prelude.equals, self.prelude.to_str].contains(&name),
            _ => false,
        }
    }

    /// The structural member `key` names, first asked for at `at`.
    pub(super) fn structural_function(
        &mut self,
        key: &FunctionKey,
        at: At,
    ) -> Result<Function, Refusal> {
        let member = Some(key.name);
        let receiver = &key.signature.parameters[0];
        let answer = key.signature.result.as_ref();
        let shapes = Shape::of(receiver);
        let mut clauses = Vec::with_capacity(shapes.len() + 1);
        if member == self.prelude.to_str {
            for shape in shapes {
                let shape = shape.by_name(self.symbols);
                clauses.push(self.shown(key.name, at, &shape)?);
            }
        } else if member == self.prelude.hash_into {
            for shape in &shapes {
                clauses.push(self.fed(key.name, at, answer, shape)?);
            }
        } else {
            for shape in &shapes {
                clauses.push(self.componentwise(key.name, at, answer, shape)?);
            }
            // Two different tags, where there are two to differ.
            if matches!(receiver, Type::Variants(tags) if tags.len() != 1) {
                let unequal = expr(
                    at,
                    answer,
                    ExprKind::Construct(self.prelude.bool_false, Vec::new()),
                );
                clauses.push(clause(vec![Pattern::Wild, Pattern::Wild], unequal));
            }
        }
        Ok(Function {
            key: key.clone(),
            definition: Definition::Body(clauses),
        })
    }

    /// `to_str` of one shape, as Ori writes it: a tag's name, its fields'
    /// own text after it in parentheses, `Invalid(3)`; a tuple's members in
    /// parentheses, `(1, "a")`; a record's fields after their names in
    /// braces, in the order of their names, `{x: 1, y: 2}`.
    fn shown(&mut self, member: Symbol, at: At, shape: &Shape) -> Result<Clause, Refusal> {
        let (open, close, empty) = match &shape.kind {
            Kind::Tag(label) => {
                let name = self.symbols.text(*label);
                (format!("{name}("), ")", name.to_owned())
            }
            Kind::Tuple => ("(".to_owned(), ")", "()".to_owned()),
            Kind::Record(_) => ("{".to_owned(), "}", "{}".to_owned()),
        };
        let names = match &shape.kind {
            Kind::Record(names) => names.iter().map(Some).collect(),
            Kind::Tag(_) | Kind::Tuple => vec![None; shape.components.len()],
        };
        let str_ = Type::Named(self.prelude.str_, Vec::new());
        let count = components(shape)?;
        let mut pieces = Vec::new();
        let mut before = open;
        for ((index, component), name) in (0..count).zip(&shape.components).zip(names) {
            if let Some(name) = name {
                before.push_str(self.symbols.text(*name));
                before.push_str(": ");
            }
            pieces.push(self.text(at, &before)?);
            let field = local(at, index, component);
            pieces.push(self.component(member, at, component, &[], &str_, vec![field])?);
            ", ".clone_into(&mut before);
        }
        let closing = if count == 0 { empty } else { close.to_owned() };
        pieces.push(self.text(at, &closing)?);
        let concat = self.method_key(
            self.prelude.str_concat,
            &str_,
            std::slice::from_ref(&str_),
            &str_,
        )?;
        let mut pieces = pieces.into_iter();
        let mut result = pieces
            .next()
            .ok_or_else(|| error("a shape is shown as something"))?;
        for next in pieces {
            self.request(concat.clone());
            result = expr(
                at,
                &str_,
                ExprKind::DirectCall(concat.clone(), vec![result, next]),
            );
        }
        Ok(clause(vec![shape.pattern(0)], result))
    }

    /// `equals` or `cmp` of two values of one shape: each pair of
    /// components compared by its type's own member, the first deciding
    /// first, joined by `&` or by `Order.or`. Past `&` a pair is compared
    /// only where those before it were equal.
    fn componentwise(
        &mut self,
        member: Symbol,
        at: At,
        answer: &Type,
        shape: &Shape,
    ) -> Result<Clause, Refusal> {
        let count = components(shape)?;
        let mut compared = Vec::with_capacity(shape.components.len());
        for (index, component) in (0..count).zip(&shape.components) {
            let sides = vec![
                local(at, index, component),
                local(at, count + index, component),
            ];
            let others = std::slice::from_ref(component);
            compared.push(self.component(member, at, component, others, answer, sides)?);
        }
        let (join, unit) = if Some(member) == self.prelude.cmp {
            (Some(self.prelude.order_or), self.prelude.order_eq)
        } else {
            (None, self.prelude.bool_true)
        };
        let join = join
            .map(|join| self.method_key(join, answer, std::slice::from_ref(answer), answer))
            .transpose()?;
        let mut result = expr(at, answer, ExprKind::Construct(unit, Vec::new()));
        if let Some(last) = compared.pop() {
            result = last;
            if let Some(join) = &join {
                self.request(join.clone());
            }
        }
        // From the last position back, so the first decides first.
        while let Some(earlier) = compared.pop() {
            let joined = match &join {
                Some(join) => ExprKind::DirectCall(join.clone(), vec![earlier, result]),
                None => ExprKind::Connective(Connective::And, Box::new(earlier), Box::new(result)),
            };
            result = expr(at, answer, joined);
        }
        Ok(clause(vec![shape.pattern(0), shape.pattern(count)], result))
    }

    /// `hash_into` of one shape: each component fed to the hasher beside it
    /// by its type's own `hash_into`, first to last, and the hasher fed.
    fn fed(
        &mut self,
        member: Symbol,
        at: At,
        hasher: &Type,
        shape: &Shape,
    ) -> Result<Clause, Refusal> {
        let count = components(shape)?;
        let mut result = local(at, count, hasher);
        for (index, component) in (0..count).zip(&shape.components) {
            let arguments = vec![local(at, index, component), result];
            let others = std::slice::from_ref(hasher);
            result = self.component(member, at, component, others, hasher, arguments)?;
        }
        let patterns = vec![shape.pattern(0), Pattern::Bind(h::LocalId(count))];
        Ok(clause(patterns, result))
    }

    /// A string literal of `text`.
    fn text(&mut self, (module, span): At, text: &str) -> Result<Expr, Refusal> {
        let literal = crate::blessed::string(text.as_bytes(), self.prelude);
        let str_ = Type::Named(self.prelude.str_, Vec::new());
        self.literal(module, span, &literal, &str_)
    }

    /// A call of `component`'s own `member`, taking `others` after it and
    /// answering `answer`, on `arguments`.
    fn component(
        &mut self,
        member: Symbol,
        at: At,
        component: &Type,
        others: &[Type],
        answer: &Type,
        arguments: Vec<Expr>,
    ) -> Result<Expr, Refusal> {
        let target = self.implementation(component, member)?;
        let call = self.method_key(target, component, others, answer)?;
        self.request_at(call.clone(), at)?;
        Ok(expr(at, answer, ExprKind::DirectCall(call, arguments)))
    }
}

/// How many components `shape` has, as locals count.
fn components(shape: &Shape) -> Result<u32, Refusal> {
    u32::try_from(shape.components.len()).map_err(|_| error("a shape has too many components"))
}

fn local(at: At, index: u32, ty: &Type) -> Expr {
    expr(at, ty, ExprKind::Local(h::LocalId(index)))
}

fn expr((module, span): At, ty: &Type, kind: ExprKind) -> Expr {
    Expr {
        module,
        span,
        ty: ty.clone(),
        kind,
    }
}

/// A clause taking `patterns` apart and answering `result`.
const fn clause(patterns: Vec<Pattern>, result: Expr) -> Clause {
    Clause {
        patterns,
        guard: None,
        body: Body {
            bindings: Vec::new(),
            result,
        },
    }
}
