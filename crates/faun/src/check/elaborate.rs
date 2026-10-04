//! Consume inference facts into typed HIR before releasing the resolved syntax.

use super::{Facts, InferredType, Reading};
use crate::ast::{BinaryOp, Span};
use crate::blessed::{self, PreludeIds};
use crate::hir as h;
use crate::typed as t;

pub(super) fn finish(
    program: crate::declarations::Program,
    mut facts: Facts,
    prelude: &PreludeIds,
    sites: &mut h::Sites,
) -> t::Program {
    let mut members = std::mem::take(&mut facts.unsigned_members);
    let mut elaborator = Elaborator {
        facts,
        prelude,
        sites,
    };
    let functions = program
        .functions
        .into_iter()
        .map(|function| {
            if let (Some(owner), Some(signature)) = (function.owner, &function.signature) {
                members.insert((owner, signature.spelling), function.name);
            }
            let span = function.clauses.first().map_or_else(
                || {
                    function
                        .signature
                        .as_ref()
                        .expect("a bodyless declaration has a signature")
                        .span
                },
                |clause| clause.span,
            );
            let definition = if function.clauses.is_empty() {
                t::Definition::External(
                    function
                        .signature
                        .expect("a bodyless declaration has a signature")
                        .spelling,
                )
            } else {
                t::Definition::Body(
                    function
                        .clauses
                        .into_iter()
                        .map(|clause| elaborator.clause(clause))
                        .collect(),
                )
            };
            t::Function {
                module: function.module,
                span,
                name: function.name,
                scheme: elaborator
                    .facts
                    .values
                    .remove(&function.name)
                    .expect("every definition has a scheme"),
                definition,
            }
        })
        .collect();
    t::Program {
        functions,
        data: program.data,
        members,
    }
}

struct Elaborator<'a> {
    facts: Facts,
    prelude: &'a PreludeIds,
    sites: &'a mut h::Sites,
}

impl Elaborator<'_> {
    fn clause(&mut self, clause: h::Clause) -> t::Clause {
        let (signature, bounds) = self.facts.clauses[&clause.site].clone();
        t::Clause {
            span: clause.span,
            signature,
            bounds,
            patterns: clause
                .patterns
                .into_iter()
                .map(|p| self.pattern(p))
                .collect(),
            guard: clause.guard.map(|expr| self.expr(expr)),
            body: self.body(clause.body),
            locals: clause.locals,
        }
    }

    fn body(&mut self, body: h::Body) -> t::Body {
        t::Body {
            bindings: body
                .bindings
                .into_iter()
                .map(|binding| t::Binding {
                    pattern: self.pattern(binding.pattern),
                    value: self.expr(binding.value),
                })
                .collect(),
            result: self.expr(body.result),
        }
    }

    fn pattern(&self, pattern: h::Pattern) -> t::Pattern {
        match pattern {
            h::Pattern::Wild => t::Pattern::Wild,
            h::Pattern::Bind(local) => t::Pattern::Bind(local),
            h::Pattern::Constructor(name, fields) => {
                t::Pattern::Constructor(name, fields.into_iter().map(|p| self.pattern(p)).collect())
            }
            h::Pattern::Tag(name, fields) => {
                t::Pattern::Tag(name, fields.into_iter().map(|p| self.pattern(p)).collect())
            }
            h::Pattern::Dual(dual, fields) => {
                let fields = fields.into_iter().map(|p| self.pattern(p)).collect();
                match self.facts.readings[&dual.site] {
                    Reading::Constructor(name) => t::Pattern::Constructor(name, fields),
                    Reading::Tag(name) => t::Pattern::Tag(name, fields),
                }
            }
            h::Pattern::Number {
                magnitude,
                negative,
            } => t::Pattern::Number {
                magnitude,
                negative,
            },
            h::Pattern::Range(low, high) => t::Pattern::Range(low, high),
            h::Pattern::String(bytes) => t::Pattern::String(bytes),
            h::Pattern::List(elements, rest) => t::Pattern::List(
                elements.into_iter().map(|p| self.pattern(p)).collect(),
                rest.map(|p| Box::new(self.pattern(*p))),
            ),
            h::Pattern::Record(fields, open) => t::Pattern::Record(
                fields
                    .into_iter()
                    .map(|(name, p)| (name, self.pattern(p)))
                    .collect(),
                open,
            ),
            h::Pattern::Tuple(members) => {
                t::Pattern::Tuple(members.into_iter().map(|p| self.pattern(p)).collect())
            }
            h::Pattern::Or(alternatives) => {
                t::Pattern::Or(alternatives.into_iter().map(|p| self.pattern(p)).collect())
            }
        }
    }

    /// What the member at `site` calls; `bare` where it is named with no
    /// call, `x.name`.
    fn target(&self, site: h::SiteId, bare: bool) -> t::Target {
        if let Some((owner, member)) = self.facts.bound_sites.get(&site) {
            t::Target::Bound {
                owner: owner.clone(),
                member: *member,
                bare,
            }
        } else {
            t::Target::Direct(self.facts.methods[&site])
        }
    }

    const fn generated(&mut self, span: Span, ty: InferredType, kind: t::ExprKind) -> t::Expr {
        t::Expr {
            site: self.sites.fresh(),
            span,
            ty,
            kind,
        }
    }

    fn expr(&mut self, expression: h::Expr) -> t::Expr {
        let (site, span) = (expression.site, expression.span);
        let expression = self.written_expr(expression);
        if let Some(target) = self.facts.widenings.get(&site) {
            let target = target.clone();
            self.generated(span, target, t::ExprKind::Widen(Box::new(expression)))
        } else {
            expression
        }
    }

    fn written_expr(&mut self, expression: h::Expr) -> t::Expr {
        let h::Expr { site, span, kind } = expression;
        let ty = self
            .facts
            .expressions
            .get(&site)
            .expect("checking records each expression's type")
            .clone();
        let kind = if let Some(literal) = self.facts.literals.get(&site) {
            t::ExprKind::Literal(literal.clone())
        } else if let Some(numeral) = self.facts.deferred_numerals.get(&site) {
            t::ExprKind::Numeral(numeral.clone())
        } else {
            match kind {
                h::ExprKind::Block(body) => t::ExprKind::Block(Box::new(self.body(*body))),
                h::ExprKind::Local(local) => t::ExprKind::Local(local),
                h::ExprKind::Global(name) => t::ExprKind::Function(name),
                h::ExprKind::Constructor(name) | h::ExprKind::Tag(name) => {
                    t::ExprKind::Constructor(name)
                }
                h::ExprKind::Dual(dual) => {
                    let (Reading::Constructor(name) | Reading::Tag(name)) =
                        self.facts.readings[&dual.site];
                    t::ExprKind::Constructor(name)
                }
                // `a.zero`: a bound's member that takes no parameters.
                h::ExprKind::Associated(..) => {
                    t::ExprKind::Method(self.target(site, false), Vec::new())
                }
                h::ExprKind::Number(_) | h::ExprKind::Decimal(..) => {
                    unreachable!("every numeral was elaborated or deferred")
                }
                h::ExprKind::String(parts) => {
                    let mut pieces = Vec::new();
                    for part in parts {
                        match part {
                            h::StringPart::Text(bytes) if bytes.is_empty() => {}
                            h::StringPart::Text(bytes) => {
                                let literal = blessed::string(&bytes, self.prelude);
                                pieces.push(self.generated(
                                    span,
                                    ty.clone(),
                                    t::ExprKind::Literal(literal),
                                ));
                            }
                            h::StringPart::Splice(value) => pieces.push(self.expr(value)),
                        }
                    }
                    let mut pieces = pieces.into_iter();
                    let mut joined = pieces.next().expect("an interpolated string has a splice");
                    for piece in pieces {
                        joined = self.generated(
                            span,
                            ty.clone(),
                            t::ExprKind::Method(
                                t::Target::Direct(self.prelude.str_concat),
                                vec![joined, piece],
                            ),
                        );
                    }
                    return joined;
                }
                h::ExprKind::List(elements, rest) => {
                    let mut tail = match rest {
                        Some(rest) => self.expr(*rest),
                        None => self.generated(
                            span,
                            ty.clone(),
                            t::ExprKind::Construct(self.prelude.list_nil, Vec::new()),
                        ),
                    };
                    for element in elements.into_iter().rev() {
                        let head = self.expr(element);
                        tail = self.generated(
                            span,
                            ty.clone(),
                            t::ExprKind::Construct(self.prelude.list_cons, vec![head, tail]),
                        );
                    }
                    return tail;
                }
                h::ExprKind::Record(fields) => t::ExprKind::Record(
                    fields
                        .into_iter()
                        .map(|(name, value)| (name, self.expr(value)))
                        .collect(),
                ),
                h::ExprKind::Update(base, fields) => t::ExprKind::Update(
                    Box::new(self.expr(*base)),
                    fields
                        .into_iter()
                        .map(|(name, value)| (name, self.expr(value)))
                        .collect(),
                ),
                h::ExprKind::Tuple(members) => {
                    t::ExprKind::Tuple(members.into_iter().map(|e| self.expr(e)).collect())
                }
                h::ExprKind::Lambda(patterns, body) => t::ExprKind::Lambda(
                    patterns.into_iter().map(|p| self.pattern(p)).collect(),
                    Box::new(self.expr(*body)),
                ),
                h::ExprKind::Call(head, arguments) => {
                    let arguments = arguments.into_iter().map(|e| self.expr(e)).collect();
                    match &head.kind {
                        h::ExprKind::Associated(..) => {
                            t::ExprKind::Method(self.target(site, false), arguments)
                        }
                        h::ExprKind::Constructor(name) | h::ExprKind::Tag(name) => {
                            t::ExprKind::Construct(*name, arguments)
                        }
                        h::ExprKind::Dual(dual) => {
                            let (Reading::Constructor(name) | Reading::Tag(name)) =
                                self.facts.readings[&dual.site];
                            t::ExprKind::Construct(name, arguments)
                        }
                        _ => t::ExprKind::Call(Box::new(self.expr(*head)), arguments),
                    }
                }
                h::ExprKind::Member(receiver, _) => {
                    let receiver = self.expr(*receiver);
                    match self.facts.projections.get(&site) {
                        Some(field) => t::ExprKind::Project(Box::new(receiver), *field),
                        None => t::ExprKind::Method(self.target(site, true), vec![receiver]),
                    }
                }
                h::ExprKind::Method(receiver, _, arguments) => {
                    let target = self.target(site, false);
                    let arguments = std::iter::once(*receiver)
                        .chain(arguments)
                        .map(|e| self.expr(e))
                        .collect();
                    t::ExprKind::Method(target, arguments)
                }
                h::ExprKind::Try(value) => t::ExprKind::Try(Box::new(self.expr(*value))),
                h::ExprKind::If(condition, yes, no) => t::ExprKind::If(
                    Box::new(self.expr(*condition)),
                    Box::new(self.expr(*yes)),
                    Box::new(self.expr(*no)),
                ),
                h::ExprKind::Unary(_, value) => {
                    t::ExprKind::Method(self.target(site, false), vec![self.expr(*value)])
                }
                h::ExprKind::Binary(operator, left, right) => {
                    let target = self.target(site, false);
                    let arguments = vec![self.expr(*left), self.expr(*right)];
                    let call = t::ExprKind::Method(target, arguments);
                    let view = match operator {
                        BinaryOp::Less => Some((self.prelude.order, self.prelude.order_lt)),
                        BinaryOp::LessEqual => Some((self.prelude.order, self.prelude.order_le)),
                        BinaryOp::Greater => Some((self.prelude.order, self.prelude.order_gt)),
                        BinaryOp::GreaterEqual => Some((self.prelude.order, self.prelude.order_ge)),
                        BinaryOp::NotEqual => Some((self.prelude.bool_, self.prelude.bool_not)),
                        _ => None,
                    };
                    if let Some((answer, view)) = view {
                        let compared =
                            self.generated(span, InferredType::Named(answer, Vec::new()), call);
                        t::ExprKind::Method(t::Target::Direct(view), vec![compared])
                    } else {
                        call
                    }
                }
            }
        };
        t::Expr {
            site,
            span,
            ty,
            kind,
        }
    }
}
