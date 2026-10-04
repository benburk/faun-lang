//! Bodies for the members a declared type asks for by signature alone.
//!
//! In a type's block, `equals`, `cmp`, `to_str` or `hash_into` written as a
//! signature with no clauses is the structural member of what the type holds:
//! its constructors, one after another, or the representation it wraps. A type
//! with `cmp` has `equals` from it, `Eq` and nothing else, whether it declares
//! `equals` or not, so the two cannot disagree; it may not write one. The
//! clauses are written here, before checking, so they are checked against the
//! signature, its `where` bounds included, as a written body is.

use crate::ast::{BinaryOp, Span};
use crate::blessed::PreludeIds;
use crate::declarations as n;
use crate::diagnostic::Diagnostic;
use crate::hir as h;
use crate::resolve::ResolvedProgram;
use std::collections::HashMap;

use crate::{Symbol, Symbols};

/// Write the clauses of every bodyless `equals`, `cmp`, `to_str` and
/// `hash_into` in a type's block, and each ordered type's `equals`.
///
/// # Errors
/// Refuses one whose signature is not the member's over its own type, and an
/// `equals` written beside a `cmp`.
pub(crate) fn requested(
    resolved: &mut ResolvedProgram<n::Program>,
    prelude: &PreludeIds,
) -> Result<(), Diagnostic> {
    ordered(resolved, prelude)?;
    let n::Program {
        functions, data, ..
    } = &mut resolved.program;
    for function in functions {
        let (Some(owner), Some(signature)) = (function.owner, &function.signature) else {
            continue;
        };
        if !function.clauses.is_empty() {
            continue;
        }
        let Some(member) = Member::of(signature.spelling, prelude) else {
            continue;
        };
        let data = &data[&owner];
        match derive(
            data,
            member,
            signature,
            prelude,
            &resolved.symbols,
            &mut resolved.sites,
        ) {
            Ok(clauses) => function.clauses = clauses,
            Err(message) => {
                let at = (function.module, signature.span);
                return Err(resolved.diagnostic(at.0, at.1, message));
            }
        }
    }
    Ok(())
}

/// Give each type with `cmp` its `equals`, `cmp(a, b).eq()`, under the
/// canonical name its binding already holds; one the type declares itself
/// is refused.
fn ordered(
    resolved: &mut ResolvedProgram<n::Program>,
    prelude: &PreludeIds,
) -> Result<(), Diagnostic> {
    let (Some(cmp), Some(equals)) = (prelude.cmp, prelude.equals) else {
        return Ok(());
    };
    let members = owned_members(resolved);
    let mut ordered: Vec<(Symbol, usize)> = members
        .iter()
        .filter(|((_, spelling), _)| *spelling == cmp)
        .map(|(&(owner, _), &index)| (owner, index))
        .collect();
    ordered.sort_unstable_by_key(|&(_, index)| index);
    for (owner, at) in ordered {
        if let Some(&index) = members.get(&(owner, equals)) {
            let declared = &resolved.program.functions[index];
            let type_name = spelled(owner, &resolved.symbols);
            let message = format!("`{type_name}` declares both `equals` and `cmp`");
            return Err(resolved
                .diagnostic(declared.module, declared_at(declared), message)
                .help("leave `equals` out: an ordered type's `equals` is its `cmp`'s `Eq`"));
        }
        let implied = equals_of(resolved, at, equals, prelude);
        resolved.program.functions.push(implied);
    }
    Ok(())
}

/// Each method a type's block holds, by its owner and spelling.
fn owned_members(resolved: &ResolvedProgram<n::Program>) -> HashMap<(Symbol, Symbol), usize> {
    let mut members = HashMap::new();
    for (index, function) in resolved.program.functions.iter().enumerate() {
        let Some(owner) = function.owner else {
            continue;
        };
        let spelling = resolved
            .symbols
            .text(function.name)
            .rsplit_once('.')
            .and_then(|(_, spelled)| resolved.symbols.find(spelled));
        if let Some(spelling) = spelling {
            members.insert((owner, spelling), index);
        }
    }
    members
}

/// The `equals` of the type whose `cmp` is function `at`: signed as it is,
/// answering a `Bool`, with its bounds.
fn equals_of(
    resolved: &mut ResolvedProgram<n::Program>,
    at: usize,
    equals: Symbol,
    prelude: &PreludeIds,
) -> n::Function {
    let order = &resolved.program.functions[at];
    let (module, owner, order_name, span) =
        (order.module, order.owner, order.name, declared_at(order));
    let text = resolved.symbols.text(order_name);
    let type_path = text.strip_suffix("cmp").unwrap_or(text).to_owned();
    let name = resolved.symbols.intern(&format!("{type_path}equals"));
    let order = &resolved.program.functions[at];
    let signature = order.signature.as_ref().map(|signature| h::SignatureDecl {
        span: signature.span,
        name,
        spelling: equals,
        parameters: signature.parameters.clone(),
        result: h::Type::Named(prelude.bool_, Vec::new()),
        constraints: signature.constraints.clone(),
    });
    let clause = equal_order(order_name, name, span, prelude, &mut resolved.sites);
    n::Function {
        module,
        name,
        owner,
        signature,
        clauses: vec![clause],
    }
}

/// Where `function` is declared: its signature, or its first clause.
fn declared_at(function: &n::Function) -> Span {
    function.signature.as_ref().map_or_else(
        || {
            function
                .clauses
                .first()
                .map(|clause| clause.span)
                .unwrap_or_default()
        },
        |signature| signature.span,
    )
}

/// `name(a, b) -> order(a, b).eq()`.
fn equal_order(
    order: Symbol,
    name: Symbol,
    span: Span,
    prelude: &PreludeIds,
    sites: &mut h::Sites,
) -> h::Clause {
    let left = sites.expr(span, h::ExprKind::Local(local(0)));
    let right = sites.expr(span, h::ExprKind::Local(local(1)));
    let order = sites.expr(span, h::ExprKind::Global(order));
    let compared = sites.expr(span, h::ExprKind::Call(Box::new(order), vec![left, right]));
    let eq = sites.expr(span, h::ExprKind::Global(prelude.order_is_eq));
    let result = sites.expr(span, h::ExprKind::Call(Box::new(eq), vec![compared]));
    h::Clause {
        site: sites.fresh(),
        span,
        name,
        patterns: binds(0..2),
        guard: None,
        body: h::Body {
            bindings: Vec::new(),
            result,
        },
        locals: 2,
    }
}

/// The members derivation writes.
#[derive(Clone, Copy)]
enum Member {
    Equals,
    Cmp,
    ToStr,
    HashInto,
}

impl Member {
    fn of(spelling: Symbol, prelude: &PreludeIds) -> Option<Self> {
        let spelling = Some(spelling);
        if spelling == prelude.equals {
            Some(Self::Equals)
        } else if spelling == prelude.cmp {
            Some(Self::Cmp)
        } else if spelling == prelude.to_str {
            Some(Self::ToStr)
        } else if spelling == prelude.hash_into {
            Some(Self::HashInto)
        } else {
            None
        }
    }

    /// Whether `signature` is this member over `data`: `(T, T) -> Bool`,
    /// `(T, T) -> Order`, `T -> Str` or `(T, h) -> h`.
    fn fits(self, signature: &h::SignatureDecl, data: &n::Data, prelude: &PreludeIds) -> bool {
        let own = |ty: &h::Type| matches!(ty, h::Type::Named(name, _) if *name == data.name);
        let named = |answer: Symbol| matches!(&signature.result, h::Type::Named(name, arguments) if *name == answer && arguments.is_empty());
        match (self, signature.parameters.as_slice()) {
            (Self::Equals, [a, b]) => own(a) && own(b) && named(prelude.bool_),
            (Self::Cmp, [a, b]) => own(a) && own(b) && named(prelude.order),
            (Self::ToStr, [a]) => own(a) && named(prelude.str_),
            (Self::HashInto, [a, hasher @ h::Type::Variable(_)]) => {
                own(a) && signature.result == *hasher
            }
            _ => false,
        }
    }
}

/// The clauses of `member` over `data`, as `signature` asks for it.
fn derive(
    data: &n::Data,
    member: Member,
    signature: &h::SignatureDecl,
    prelude: &PreludeIds,
    symbols: &Symbols,
    sites: &mut h::Sites,
) -> Result<Vec<h::Clause>, String> {
    let feeds = matches!(member, Member::HashInto) && prelude.write_u64.is_some();
    let fits =
        member.fits(signature, data, prelude) && (feeds || !matches!(member, Member::HashInto));
    if !fits {
        return Err(misfit(data, member, signature, symbols));
    }
    let mut writer = Writer {
        sites,
        prelude,
        span: signature.span,
        name: signature.name,
        spelling: signature.spelling,
    };
    let clauses = match (member, &data.wrapper) {
        (Member::ToStr, Some(wrapper)) => vec![writer.payload_to_str(wrapper.constructor)],
        (Member::ToStr, None) => data
            .constructors
            .iter()
            .map(|constructor| {
                let text = spelled(constructor.name, symbols);
                writer.constructor_to_str(constructor.name, text, constructor.fields.len())
            })
            .collect(),
        (Member::Equals, _) => writer.equals(&constructors(data)),
        (Member::Cmp, _) => writer.cmp(&constructors(data)),
        (Member::HashInto, _) => writer.hash_into(&constructors(data)),
    };
    Ok(clauses)
}

/// Each constructor of `data` and how many fields it has; a wrapper is one
/// constructor of one.
fn constructors(data: &n::Data) -> Vec<(Symbol, usize)> {
    data.wrapper.as_ref().map_or_else(
        || {
            data.constructors
                .iter()
                .map(|constructor| (constructor.name, constructor.fields.len()))
                .collect()
        },
        |wrapper| vec![(wrapper.constructor, 1)],
    )
}

/// Why `signature` cannot be derived: what the member is, over `data`.
fn misfit(
    data: &n::Data,
    member: Member,
    signature: &h::SignatureDecl,
    symbols: &Symbols,
) -> String {
    let mut own = spelled(data.name, symbols).to_owned();
    if !data.parameters.is_empty() {
        let parameters: Vec<&str> = data
            .parameters
            .iter()
            .map(|parameter| symbols.text(*parameter))
            .collect();
        own = format!("{own}({})", parameters.join(", "));
    }
    let expected = match member {
        Member::Equals => format!("({own}, {own}) -> Bool"),
        Member::Cmp => format!("({own}, {own}) -> Order"),
        Member::ToStr => format!("{own} -> Str"),
        Member::HashInto => format!("({own}, h) -> h"),
    };
    format!(
        "`{}` without a body is derived, and is derived only as `{expected}`",
        symbols.text(signature.spelling)
    )
}

/// What a declaration's canonical name spells in source.
fn spelled(name: Symbol, symbols: &Symbols) -> &str {
    let text = symbols.text(name);
    text.rsplit_once("$$")
        .map_or(text, |(_, spelling)| spelling)
}

/// Writes one member's clauses, each at its signature.
struct Writer<'a> {
    sites: &'a mut h::Sites,
    prelude: &'a PreludeIds,
    span: Span,
    /// The member's canonical name, and its spelling, which each field is
    /// asked for its own of.
    name: Symbol,
    spelling: Symbol,
}

impl Writer<'_> {
    /// Values of one constructor are equal where their fields are; of two,
    /// never.
    fn equals(&mut self, constructors: &[(Symbol, usize)]) -> Vec<h::Clause> {
        let mut clauses = Vec::with_capacity(constructors.len() + 1);
        for &(constructor, count) in constructors {
            let (left, right) = pair(constructor, count);
            let mut result = None;
            for index in 0..count {
                let equal = self.ask(index, count);
                result = Some(match result {
                    None => equal,
                    Some(before) => self.expr(h::ExprKind::Binary(
                        BinaryOp::And,
                        Box::new(before),
                        Box::new(equal),
                    )),
                });
            }
            let result = result
                .unwrap_or_else(|| self.expr(h::ExprKind::Constructor(self.prelude.bool_true)));
            clauses.push(self.clause(vec![left, right], result, count * 2));
        }
        if constructors.len() != 1 {
            let unequal = self.expr(h::ExprKind::Constructor(self.prelude.bool_false));
            clauses.push(self.clause(vec![h::Pattern::Wild, h::Pattern::Wild], unequal, 0));
        }
        clauses
    }

    /// Values of one constructor are ordered by their fields in turn, and of
    /// two by which the type declares first.
    fn cmp(&mut self, constructors: &[(Symbol, usize)]) -> Vec<h::Clause> {
        let mut clauses = Vec::with_capacity(constructors.len() * 3);
        for (at, &(constructor, count)) in constructors.iter().enumerate() {
            let (left, right) = pair(constructor, count);
            let mut result = None;
            for index in 0..count {
                let order = self.ask(index, count);
                result = Some(match result {
                    None => order,
                    Some(before) => {
                        let or = self.expr(h::ExprKind::Global(self.prelude.order_or));
                        self.expr(h::ExprKind::Call(Box::new(or), vec![before, order]))
                    }
                });
            }
            let result = result
                .unwrap_or_else(|| self.expr(h::ExprKind::Constructor(self.prelude.order_eq)));
            clauses.push(self.clause(vec![left, right], result, count * 2));
            // Past the last constructor, both are it.
            if at + 1 < constructors.len() {
                let any = h::Pattern::Constructor(constructor, vec![h::Pattern::Wild; count]);
                let before = self.expr(h::ExprKind::Constructor(self.prelude.order_less));
                let after = self.expr(h::ExprKind::Constructor(self.prelude.order_greater));
                clauses.push(self.clause(vec![any.clone(), h::Pattern::Wild], before, 0));
                clauses.push(self.clause(vec![h::Pattern::Wild, any], after, 0));
            }
        }
        clauses
    }

    /// Which constructor it is, by its place, where there are several to
    /// tell apart, then each field fed in turn: a wrapper feeds what it
    /// wraps.
    fn hash_into(&mut self, constructors: &[(Symbol, usize)]) -> Vec<h::Clause> {
        let write_u64 = self
            .prelude
            .write_u64
            .expect("a derived `hash_into` is asked only where `write_u64` is spelled");
        let mut clauses = Vec::with_capacity(constructors.len());
        for (at, &(constructor, count)) in constructors.iter().enumerate() {
            let mut fed = self.local(count);
            if constructors.len() > 1 {
                let place = self.expr(h::ExprKind::Number(at.into()));
                fed = self.expr(h::ExprKind::Method(Box::new(fed), write_u64, vec![place]));
            }
            for index in 0..count {
                let field = self.local(index);
                fed = self.expr(h::ExprKind::Method(
                    Box::new(field),
                    self.spelling,
                    vec![fed],
                ));
            }
            let patterns = vec![
                h::Pattern::Constructor(constructor, binds(0..count)),
                h::Pattern::Bind(local(count)),
            ];
            clauses.push(self.clause(patterns, fed, count + 1));
        }
        clauses
    }

    /// A constructor's name, and after it each field's own text in
    /// parentheses, `Filled(1, 2)`; a constructor without fields is its name.
    fn constructor_to_str(&mut self, constructor: Symbol, name: &str, count: usize) -> h::Clause {
        let mut parts = Vec::with_capacity(count * 2 + 1);
        if count == 0 {
            parts.push(h::StringPart::Text(name.as_bytes().to_vec()));
        } else {
            for index in 0..count {
                let before = if index == 0 {
                    format!("{name}(")
                } else {
                    ", ".to_owned()
                };
                parts.push(h::StringPart::Text(before.into_bytes()));
                parts.push(h::StringPart::Splice(self.field_to_str(index)));
            }
            parts.push(h::StringPart::Text(b")".to_vec()));
        }
        let text = self.expr(h::ExprKind::String(parts));
        let pattern = h::Pattern::Constructor(constructor, binds(0..count));
        self.clause(vec![pattern], text, count)
    }

    /// A wrapper's text is its payload's.
    fn payload_to_str(&mut self, constructor: Symbol) -> h::Clause {
        let text = self.field_to_str(0);
        let pattern = h::Pattern::Constructor(constructor, binds(0..1));
        self.clause(vec![pattern], text, 1)
    }

    /// The left's field `index` asked the member of the right's.
    fn ask(&mut self, index: usize, count: usize) -> h::Expr {
        let left = self.local(index);
        let right = self.local(count + index);
        self.expr(h::ExprKind::Method(
            Box::new(left),
            self.spelling,
            vec![right],
        ))
    }

    /// Field `index`'s own text.
    fn field_to_str(&mut self, index: usize) -> h::Expr {
        let field = self.local(index);
        self.expr(h::ExprKind::Method(
            Box::new(field),
            self.spelling,
            Vec::new(),
        ))
    }

    fn local(&mut self, index: usize) -> h::Expr {
        self.expr(h::ExprKind::Local(local(index)))
    }

    const fn expr(&mut self, kind: h::ExprKind) -> h::Expr {
        self.sites.expr(self.span, kind)
    }

    /// A clause taking `patterns` to `result`, binding `bound` locals.
    fn clause(&mut self, patterns: Vec<h::Pattern>, result: h::Expr, bound: usize) -> h::Clause {
        h::Clause {
            site: self.sites.fresh(),
            span: self.span,
            name: self.name,
            patterns,
            guard: None,
            body: h::Body {
                bindings: Vec::new(),
                result,
            },
            locals: u32::try_from(bound).expect("a constructor has fewer than 2^31 fields"),
        }
    }
}

/// Both sides taken apart by `constructor`: the left's fields bound first,
/// then the right's.
fn pair(constructor: Symbol, count: usize) -> (h::Pattern, h::Pattern) {
    (
        h::Pattern::Constructor(constructor, binds(0..count)),
        h::Pattern::Constructor(constructor, binds(count..count * 2)),
    )
}

fn binds(indices: std::ops::Range<usize>) -> Vec<h::Pattern> {
    indices
        .map(|index| h::Pattern::Bind(local(index)))
        .collect()
}

fn local(index: usize) -> h::LocalId {
    h::LocalId(u32::try_from(index).expect("a constructor has fewer than 2^31 fields"))
}
