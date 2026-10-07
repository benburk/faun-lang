//! Record builders, as Ori has them: a record literal handed alone to a
//! function whose signature pairs two values of one shape,
//! `(F(a, e), F(b, e), (a, b) -> c) -> F(c, e)`, is that function applied a
//! field at a time. `Result.map2({x: rx, y: ry})` is
//! `Result.map2(rx, ry, |x, y| {x: x, y: y})`, and each further field folds
//! in by the same function again, its combiner rebuilding the record with
//! that field added, so every step answers a record and the last is the one
//! written.
//!
//! The signature's shape is what asks for it, never a name, so any type with
//! such a pairing has builders and nothing is registered. The fields are
//! evaluated in the order written, each once.

use std::collections::HashSet;

use crate::Symbol;
use crate::hir as h;

/// Rewrite every record builder in `modules`, whose signatures have had their
/// aliases expanded.
pub(crate) fn desugar(modules: &mut [h::Module], sites: &mut h::Sites) {
    let pairings = pairings(modules);
    if pairings.is_empty() {
        return;
    }
    for module in modules {
        for item in &mut module.items {
            match item {
                h::Item::Clause(clause) => clause_builders(clause, &pairings, sites),
                h::Item::Data(data) => {
                    for method in &mut data.methods {
                        if let h::MethodItem::Clause(clause) = method {
                            clause_builders(clause, &pairings, sites);
                        }
                    }
                }
                h::Item::Signature(_) => {}
            }
        }
    }
}

/// The functions whose signatures pair two values of one shape.
fn pairings(modules: &[h::Module]) -> HashSet<Symbol> {
    let signatures = modules
        .iter()
        .flat_map(|module| &module.items)
        .flat_map(|item| {
            let own: Box<dyn Iterator<Item = &h::SignatureDecl>> = match item {
                h::Item::Signature(signature) => Box::new(std::iter::once(signature)),
                h::Item::Data(data) => {
                    Box::new(data.methods.iter().filter_map(|method| match method {
                        h::MethodItem::Signature(signature) => Some(signature),
                        h::MethodItem::Clause(_) => None,
                    }))
                }
                h::Item::Clause(_) => Box::new(std::iter::empty()),
            };
            own
        });
    signatures
        .filter(|signature| pairs(signature))
        .map(|signature| signature.name)
        .collect()
}

/// Whether `signature` is `(F(a, e), F(b, e), (a, b) -> c) -> F(c, e)`.
fn pairs(signature: &h::SignatureDecl) -> bool {
    let [
        h::Type::Named(shape, first),
        h::Type::Named(other, second),
        h::Type::Function(combined, answer),
    ] = signature.parameters.as_slice()
    else {
        return false;
    };
    let h::Type::Named(result, produced) = &signature.result else {
        return false;
    };
    let (
        Some((h::Type::Variable(a), rest)),
        Some((h::Type::Variable(b), other_rest)),
        Some((h::Type::Variable(c), result_rest)),
    ) = (
        first.split_first(),
        second.split_first(),
        produced.split_first(),
    )
    else {
        return false;
    };
    shape == other
        && shape == result
        && a != b
        && rest == other_rest
        && rest == result_rest
        && combined.as_slice() == [h::Type::Variable(*a), h::Type::Variable(*b)]
        && **answer == h::Type::Variable(*c)
}

fn clause_builders(clause: &mut h::Clause, pairings: &HashSet<Symbol>, sites: &mut h::Sites) {
    let mut builder = Builder {
        pairings,
        sites,
        next: clause.locals,
    };
    if let Some(guard) = &mut clause.guard {
        builder.expr(guard);
    }
    builder.body(&mut clause.body);
    clause.locals = builder.next;
}

struct Builder<'a> {
    sites: &'a mut h::Sites,
    pairings: &'a HashSet<Symbol>,
    /// The next local the clause has not used.
    next: u32,
}

impl Builder<'_> {
    const fn fresh(&mut self) -> h::LocalId {
        let local = h::LocalId(self.next);
        self.next = self.next.checked_add(1).expect("fewer than 2^32 locals");
        local
    }

    fn body(&mut self, body: &mut h::Body) {
        for binding in &mut body.bindings {
            self.expr(&mut binding.value);
        }
        self.expr(&mut body.result);
    }

    fn exprs<'e>(&mut self, expressions: impl IntoIterator<Item = &'e mut h::Expr>) {
        for expression in expressions {
            self.expr(expression);
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one arm per expression form, which the walk must reach into"
    )]
    fn expr(&mut self, expression: &mut h::Expr) {
        match &mut expression.kind {
            h::ExprKind::Block(body) => {
                for binding in &mut body.bindings {
                    self.expr(&mut binding.value);
                }
                self.expr(&mut body.result);
            }
            h::ExprKind::Local(_)
            | h::ExprKind::Global(_)
            | h::ExprKind::Constructor(_)
            | h::ExprKind::Tag(_)
            | h::ExprKind::Associated(..)
            | h::ExprKind::Dual(_)
            | h::ExprKind::Number(_)
            | h::ExprKind::Decimal(..) => {}
            h::ExprKind::String(parts) => {
                for part in parts {
                    if let h::StringPart::Splice(inner) = part {
                        self.expr(inner);
                    }
                }
            }
            h::ExprKind::List(elements, rest) => {
                self.exprs(elements.iter_mut());
                if let Some(rest) = rest {
                    self.expr(rest);
                }
            }
            h::ExprKind::Record(fields) => self.exprs(fields.iter_mut().map(|(_, value)| value)),
            h::ExprKind::Update(base, fields) => {
                self.expr(base);
                self.exprs(fields.iter_mut().map(|(_, value)| value));
            }
            h::ExprKind::Tuple(members) => self.exprs(members.iter_mut()),
            h::ExprKind::Lambda(_, body)
            | h::ExprKind::Try(body)
            | h::ExprKind::Return(body)
            | h::ExprKind::Unary(_, body) => {
                self.expr(body);
            }
            h::ExprKind::Member(head, _) => self.expr(head),
            h::ExprKind::Method(head, _, arguments) => {
                self.expr(head);
                self.exprs(arguments.iter_mut());
            }
            h::ExprKind::Binary(_, left, right) => {
                self.expr(left);
                self.expr(right);
            }
            h::ExprKind::Is(value, _) => self.expr(value),
            h::ExprKind::Match(value, arms) => {
                self.expr(value);
                for arm in arms {
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&mut arm.body);
                }
            }
            h::ExprKind::If(condition, yes, no) => {
                self.expr(condition);
                self.expr(yes);
                self.expr(no);
            }
            h::ExprKind::Call(head, arguments) => {
                self.expr(head);
                self.exprs(arguments.iter_mut());
                if let Some(built) = self.built(expression.span, head, arguments) {
                    expression.kind = built;
                }
            }
        }
    }

    /// `head(record)` a field at a time, where `head` pairs values and
    /// `record` is a literal of two fields or more.
    fn built(
        &mut self,
        span: crate::ast::Span,
        head: &h::Expr,
        arguments: &[h::Expr],
    ) -> Option<h::ExprKind> {
        let h::ExprKind::Global(function) = head.kind else {
            return None;
        };
        let [
            h::Expr {
                kind: h::ExprKind::Record(fields),
                ..
            },
        ] = arguments
        else {
            return None;
        };
        if !self.pairings.contains(&function) || fields.len() < 2 {
            return None;
        }
        let names: Vec<Symbol> = fields.iter().map(|(name, _)| *name).collect();
        let first = self.first_pair(span, &names[..2]);
        let mut built = h::ExprKind::Call(
            Box::new(self.sites.expr(span, head.kind.clone())),
            vec![fields[0].1.clone(), fields[1].1.clone(), first],
        );
        // Each further one pairs with the record so far, rebuilt with it.
        for count in 2..fields.len() {
            let combine = self.next_pair(span, &names[..count], names[count]);
            let so_far = self.sites.expr(span, built);
            built = h::ExprKind::Call(
                Box::new(self.sites.expr(span, head.kind.clone())),
                vec![so_far, fields[count].1.clone(), combine],
            );
        }
        Some(built)
    }

    /// `|a, b| {x: a, y: b}`: the first two fields paired as they are.
    fn first_pair(&mut self, span: crate::ast::Span, names: &[Symbol]) -> h::Expr {
        let (first, second) = (self.fresh(), self.fresh());
        let record = h::ExprKind::Record(vec![
            (names[0], self.sites.expr(span, h::ExprKind::Local(first))),
            (names[1], self.sites.expr(span, h::ExprKind::Local(second))),
        ]);
        let record = self.sites.expr(span, record);
        self.sites.expr(
            span,
            h::ExprKind::Lambda(
                vec![h::Pattern::Bind(first), h::Pattern::Bind(second)],
                Box::new(record),
            ),
        )
    }

    /// `|r, z| {x: r.x, y: r.y, z: z}`: the record so far, rebuilt with the
    /// field `added`.
    fn next_pair(&mut self, span: crate::ast::Span, earlier: &[Symbol], added: Symbol) -> h::Expr {
        let (so_far, value) = (self.fresh(), self.fresh());
        let mut rebuilt = Vec::with_capacity(earlier.len() + 1);
        for &name in earlier {
            let read = self.sites.expr(span, h::ExprKind::Local(so_far));
            rebuilt.push((
                name,
                self.sites
                    .expr(span, h::ExprKind::Member(Box::new(read), name)),
            ));
        }
        rebuilt.push((added, self.sites.expr(span, h::ExprKind::Local(value))));
        let record = self.sites.expr(span, h::ExprKind::Record(rebuilt));
        self.sites.expr(
            span,
            h::ExprKind::Lambda(
                vec![h::Pattern::Bind(so_far), h::Pattern::Bind(value)],
                Box::new(record),
            ),
        )
    }
}
