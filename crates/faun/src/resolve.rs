//! Resolve module-local source names into canonical globals and compact locals.

// Resolution is a pair of cohesive exhaustive walks. Keeping each match whole
// makes omissions visible when surface syntax gains a variant.
#![allow(clippy::too_many_lines)]

use std::collections::HashMap;
use std::fmt;

use super::ast as s;
use super::diagnostic::Diagnostic;
use super::hir as h;
use super::literal;
use super::modules::{Interface, LoadedModule, LoadedProgram, ModuleId, TypeBinding};
use super::{SourceId, Sources, Symbol, Symbols};

#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    pub sources: Sources,
    pub symbols: Symbols,
    pub program: h::Program,
    /// Each module's source, by module.
    module_sources: Vec<SourceId>,
}

impl ResolvedProgram {
    /// A diagnostic at `span` in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn diagnostic(&self, module: ModuleId, span: s::Span, message: String) -> Diagnostic {
        let source = self.module_sources[module.index()];
        let source = self
            .sources
            .get(source)
            .expect("a resolved module has a source");
        Diagnostic::new(message).at(source, span)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveError {
    pub module: ModuleId,
    pub span: s::Span,
    pub message: String,
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ResolveError {}

/// Resolve every loaded module without mutating or concatenating its surface AST.
///
/// # Errors
///
/// Reports an unknown or duplicate local, global, constructor, type, or method,
/// at the span it is written.
///
/// # Panics
///
/// Panics only if a [`LoadedProgram`] was manually built with a module whose
/// source identity is absent from its source collection.
pub fn resolve(mut loaded: LoadedProgram) -> Result<ResolvedProgram, Diagnostic> {
    let prelude = loaded
        .prelude
        .map(|id| loaded.module(id).public.clone())
        .unwrap_or_default();
    let mut modules = Vec::with_capacity(loaded.modules.len());
    for module in &loaded.modules {
        let source = loaded
            .sources
            .get(module.source)
            .expect("loaded module has source")
            .text();
        let mut scope = prelude.clone();
        scope.merge(&module.scope, &loaded.symbols, "module scope")?;
        let resolved = resolve_module(module, source, &scope, &mut loaded.symbols);
        modules.push(resolved.map_err(|error| {
            let source = loaded
                .sources
                .get(module.source)
                .expect("loaded module has source");
            Diagnostic::new(error.message).at(source, error.span)
        })?);
    }
    Ok(ResolvedProgram {
        module_sources: loaded.modules.iter().map(|module| module.source).collect(),
        sources: loaded.sources,
        symbols: loaded.symbols,
        program: h::Program { modules },
    })
}

fn resolve_module(
    module: &LoadedModule,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::Module, ResolveError> {
    let mut items = Vec::new();
    for item in &module.syntax.items {
        match item {
            s::Item::Data(data) => items.push(h::Item::Data(resolve_data(
                module.id, data, source, scope, symbols,
            )?)),
            s::Item::Signature(signature) => {
                let name = global_value(module.id, signature.name, source, scope, symbols)?;
                items.push(h::Item::Signature(resolve_signature(
                    module.id, signature, name, source, scope, symbols,
                )?));
            }
            s::Item::Clause(clause) => {
                let name = global_value(module.id, clause.name, source, scope, symbols)?;
                items.push(h::Item::Clause(resolve_clause(
                    module.id, clause, name, source, scope, None, symbols,
                )?));
            }
            s::Item::Header(_) | s::Item::Import(_) | s::Item::Exports(_) => {}
        }
    }
    let mut visible_methods: Vec<_> = scope
        .types
        .values()
        .flat_map(|binding| binding.methods.values().copied())
        .collect();
    visible_methods.sort_unstable();
    visible_methods.dedup();
    Ok(h::Module {
        source: module.id,
        visible_methods,
        items,
    })
}

fn resolve_data(
    module: ModuleId,
    data: &s::DataDecl,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::DataDecl, ResolveError> {
    let local = symbols
        .find(data.name.text(source))
        .expect("declaration collection interns type names");
    let binding = scope.types.get(&local).ok_or_else(|| {
        error(
            module,
            data.name.0,
            format!("unknown type `{}`", data.name.text(source)),
        )
    })?;
    let parameters = data
        .params
        .iter()
        .map(|parameter| symbols.intern(parameter.text(source)))
        .collect();
    let (constructors, wrapper) = match &data.representation {
        s::DataRepresentation::Sum(constructors) => (
            constructors
                .iter()
                .map(|constructor| {
                    let spelling = symbols.intern(constructor.name.text(source));
                    let name = binding.constructors[&spelling];
                    let fields = constructor
                        .fields
                        .iter()
                        .map(|field| resolve_type(module, field, source, scope, symbols))
                        .collect::<Result<_, _>>()?;
                    Ok(h::ConstructorDecl { name, fields })
                })
                .collect::<Result<_, ResolveError>>()?,
            None,
        ),
        s::DataRepresentation::Wrapper(representation) => (
            Vec::new(),
            Some(h::WrapperDecl {
                constructor: binding.constructors[&local],
                field: resolve_type(module, representation, source, scope, symbols)?,
            }),
        ),
    };
    let mut methods = Vec::with_capacity(data.methods.len());
    for method in &data.methods {
        match method {
            s::MethodItem::Signature(signature) => {
                let name = method_name(module, signature.name, source, binding, symbols)?;
                methods.push(h::MethodItem::Signature(resolve_signature(
                    module, signature, name, source, scope, symbols,
                )?));
            }
            s::MethodItem::Clause(clause) => {
                let name = method_name(module, clause.name, source, binding, symbols)?;
                methods.push(h::MethodItem::Clause(resolve_clause(
                    module,
                    clause,
                    name,
                    source,
                    scope,
                    Some(binding),
                    symbols,
                )?));
            }
        }
    }
    Ok(h::DataDecl {
        span: data.span,
        name: binding.canonical,
        parameters,
        constructors,
        wrapper,
        methods,
    })
}

fn resolve_signature(
    module: ModuleId,
    signature: &s::SignatureDecl,
    name: Symbol,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::SignatureDecl, ResolveError> {
    Ok(h::SignatureDecl {
        span: signature.span,
        name,
        spelling: symbols.intern(signature.name.text(source)),
        parameters: signature
            .parameters
            .iter()
            .map(|ty| resolve_type(module, ty, source, scope, symbols))
            .collect::<Result<_, _>>()?,
        result: resolve_type(module, &signature.result, source, scope, symbols)?,
        constraints: signature
            .constraints
            .iter()
            .map(|constraint| {
                Ok(h::Constraint {
                    name: symbols.intern(constraint.name.text(source)),
                    arguments: constraint
                        .arguments
                        .iter()
                        .map(|ty| resolve_type(module, ty, source, scope, symbols))
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, ResolveError>>()?,
    })
}

fn resolve_type(
    module: ModuleId,
    ty: &s::Type,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::Type, ResolveError> {
    match ty {
        s::Type::Named {
            span,
            name,
            arguments,
        } => {
            let spelling = symbols.intern(name.text(source));
            let arguments: Vec<h::Type> = arguments
                .iter()
                .map(|argument| resolve_type(module, argument, source, scope, symbols))
                .collect::<Result<_, _>>()?;
            if name
                .text(source)
                .starts_with(|character: char| character.is_ascii_lowercase())
            {
                if arguments.is_empty() {
                    Ok(h::Type::Variable(spelling))
                } else {
                    Err(error(
                        module,
                        *span,
                        "a type variable cannot take arguments",
                    ))
                }
            } else {
                scope
                    .types
                    .get(&spelling)
                    .map(|binding| h::Type::Named(binding.canonical, arguments))
                    .ok_or_else(|| {
                        error(
                            module,
                            *span,
                            format!("unknown type `{}`", name.text(source)),
                        )
                    })
            }
        }
        s::Type::Function {
            parameters, result, ..
        } => Ok(h::Type::Function(
            parameters
                .iter()
                .map(|parameter| resolve_type(module, parameter, source, scope, symbols))
                .collect::<Result<_, _>>()?,
            Box::new(resolve_type(module, result, source, scope, symbols)?),
        )),
        s::Type::Variants { constructors, .. } => Ok(h::Type::Variants(
            constructors
                .iter()
                .map(|constructor| {
                    Ok(h::ConstructorDecl {
                        name: symbols.intern(constructor.name.text(source)),
                        fields: constructor
                            .fields
                            .iter()
                            .map(|field| resolve_type(module, field, source, scope, symbols))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, ResolveError>>()?,
        )),
        s::Type::Record { span, fields } => {
            let mut resolved = fields
                .iter()
                .map(|(name, ty)| {
                    Ok((
                        symbols.intern(name.text(source)),
                        resolve_type(module, ty, source, scope, symbols)?,
                    ))
                })
                .collect::<Result<Vec<_>, ResolveError>>()?;
            resolved.sort_by_key(|(name, _)| *name);
            if resolved.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                return Err(error(module, *span, "record type repeats a field"));
            }
            Ok(h::Type::Record(resolved))
        }
    }
}

fn resolve_clause(
    module: ModuleId,
    clause: &s::Clause,
    name: Symbol,
    source: &str,
    scope: &Interface,
    methods: Option<&TypeBinding>,
    symbols: &mut Symbols,
) -> Result<h::Clause, ResolveError> {
    let mut resolver = ClauseResolver {
        module,
        source,
        scope,
        methods,
        symbols,
        locals: HashMap::new(),
        next_local: 0,
    };
    let patterns = clause
        .patterns
        .iter()
        .map(|pattern| resolver.pattern(pattern))
        .collect::<Result<_, _>>()?;
    let guard = clause
        .guard
        .as_ref()
        .map(|guard| resolver.expr(guard))
        .transpose()?;
    let mut bindings = Vec::with_capacity(clause.body.bindings.len());
    for binding in &clause.body.bindings {
        let value = resolver.expr(&binding.value)?;
        let pattern = resolver.pattern(&binding.pattern)?;
        bindings.push(h::Binding { pattern, value });
    }
    let result = resolver.expr(&clause.body.result)?;
    Ok(h::Clause {
        span: clause.span,
        name,
        patterns,
        guard,
        body: h::Body { bindings, result },
        locals: resolver.next_local,
    })
}

struct ClauseResolver<'a> {
    module: ModuleId,
    source: &'a str,
    scope: &'a Interface,
    methods: Option<&'a TypeBinding>,
    symbols: &'a mut Symbols,
    locals: HashMap<Symbol, h::LocalId>,
    next_local: u32,
}

impl ClauseResolver<'_> {
    fn pattern(&mut self, pattern: &s::Pattern) -> Result<h::Pattern, ResolveError> {
        match pattern {
            s::Pattern::Wild(_) => Ok(h::Pattern::Wild),
            s::Pattern::Bind(name) => {
                let spelling = self.symbols.intern(name.text(self.source));
                if self.locals.contains_key(&spelling) {
                    return Err(error(
                        self.module,
                        name.0,
                        format!("local `{}` is bound more than once", name.text(self.source)),
                    ));
                }
                let local = h::LocalId(self.next_local);
                self.next_local = self
                    .next_local
                    .checked_add(1)
                    .expect("fewer than 2^32 locals");
                self.locals.insert(spelling, local);
                Ok(h::Pattern::Bind(local))
            }
            s::Pattern::Constructor { span, name, fields } => {
                let spelling = self.symbols.intern(name.text(self.source));
                let constructor =
                    self.scope
                        .constructors
                        .get(&spelling)
                        .copied()
                        .ok_or_else(|| {
                            error(
                                self.module,
                                *span,
                                format!("unknown constructor `{}`", name.text(self.source)),
                            )
                        })?;
                Ok(h::Pattern::Constructor(
                    constructor,
                    fields
                        .iter()
                        .map(|field| self.pattern(field))
                        .collect::<Result<_, _>>()?,
                ))
            }
            s::Pattern::Number {
                numeral, negative, ..
            } => Ok(h::Pattern::Number {
                magnitude: literal::magnitude(*numeral, self.source)
                    .expect("literals were validated while parsing"),
                negative: *negative,
            }),
            s::Pattern::Range { start, end, .. } => Ok(h::Pattern::Range(
                literal::magnitude(*start, self.source)
                    .expect("literals were validated while parsing"),
                literal::magnitude(*end, self.source)
                    .expect("literals were validated while parsing"),
            )),
            s::Pattern::List { elements, rest, .. } => Ok(h::Pattern::List(
                elements
                    .iter()
                    .map(|element| self.pattern(element))
                    .collect::<Result<_, _>>()?,
                rest.as_deref()
                    .map(|rest| self.pattern(rest).map(Box::new))
                    .transpose()?,
            )),
            s::Pattern::Record { span, fields } => {
                let mut resolved = fields
                    .iter()
                    .map(|(name, pattern)| {
                        Ok((
                            self.symbols.intern(name.text(self.source)),
                            self.pattern(pattern)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, ResolveError>>()?;
                resolved.sort_by_key(|(name, _)| *name);
                if resolved.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                    return Err(error(self.module, *span, "record pattern repeats a field"));
                }
                Ok(h::Pattern::Record(resolved))
            }
        }
    }

    fn expr(&mut self, expression: &s::Expr) -> Result<h::Expr, ResolveError> {
        let kind = match &expression.kind {
            s::ExprKind::Name(name) => self.name(*name)?,
            s::ExprKind::Number(numeral) => h::ExprKind::Number(
                literal::magnitude(*numeral, self.source)
                    .expect("literals were validated while parsing"),
            ),
            s::ExprKind::String(parts) => h::ExprKind::String(
                parts
                    .iter()
                    .map(|part| match part {
                        s::StringPart::Text(span) => Ok(h::StringPart::Text(
                            literal::decode_text(span.text(self.source))
                                .expect("literals were validated while parsing")
                                .as_bytes()
                                .to_vec(),
                        )),
                        s::StringPart::Splice(expression) => {
                            Ok(h::StringPart::Splice(self.expr(expression)?))
                        }
                    })
                    .collect::<Result<_, ResolveError>>()?,
            ),
            s::ExprKind::List(elements, rest) => h::ExprKind::List(
                elements
                    .iter()
                    .map(|element| self.expr(element))
                    .collect::<Result<_, _>>()?,
                rest.as_deref()
                    .map(|rest| self.expr(rest).map(Box::new))
                    .transpose()?,
            ),
            s::ExprKind::Record(fields) => {
                let mut seen = std::collections::HashSet::new();
                let mut resolved = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    let name = self.symbols.intern(name.text(self.source));
                    if !seen.insert(name) {
                        return Err(error(
                            self.module,
                            expression.span,
                            "record expression repeats a field",
                        ));
                    }
                    resolved.push((name, self.expr(value)?));
                }
                h::ExprKind::Record(resolved)
            }
            s::ExprKind::Lambda(patterns, body) => {
                let saved = self.locals.clone();
                let patterns = patterns
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<_, _>>()?;
                let body = self.expr(body)?;
                self.locals = saved;
                h::ExprKind::Lambda(patterns, Box::new(body))
            }
            s::ExprKind::Call(head, arguments) => h::ExprKind::Call(
                Box::new(self.expr(head)?),
                arguments
                    .iter()
                    .map(|argument| self.expr(argument))
                    .collect::<Result<_, _>>()?,
            ),
            s::ExprKind::Member(head, member) => {
                if let Some(method) = self.static_method(head, *member) {
                    h::ExprKind::Global(method?)
                } else {
                    h::ExprKind::Member(
                        Box::new(self.expr(head)?),
                        self.symbols.intern(member.text(self.source)),
                    )
                }
            }
            s::ExprKind::Method(head, member, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.expr(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(method) = self.static_method(head, *member) {
                    h::ExprKind::Call(
                        Box::new(h::Expr {
                            span: head.span.through(member.0),
                            kind: h::ExprKind::Global(method?),
                        }),
                        arguments,
                    )
                } else {
                    h::ExprKind::Method(
                        Box::new(self.expr(head)?),
                        self.symbols.intern(member.text(self.source)),
                        arguments,
                    )
                }
            }
            s::ExprKind::Unary(operator, value) => {
                h::ExprKind::Unary(*operator, Box::new(self.expr(value)?))
            }
            s::ExprKind::Binary(operator, left, right) => h::ExprKind::Binary(
                *operator,
                Box::new(self.expr(left)?),
                Box::new(self.expr(right)?),
            ),
        };
        Ok(h::Expr {
            span: expression.span,
            kind,
        })
    }

    fn name(&mut self, name: s::Name) -> Result<h::ExprKind, ResolveError> {
        let spelling = self.symbols.intern(name.text(self.source));
        if let Some(&local) = self.locals.get(&spelling) {
            return Ok(h::ExprKind::Local(local));
        }
        if let Some(&global) = self.scope.values.get(&spelling) {
            return Ok(h::ExprKind::Global(global));
        }
        if let Some(methods) = self.methods
            && let Some(&method) = methods.methods.get(&spelling)
        {
            return Ok(h::ExprKind::Global(method));
        }
        if let Some(&constructor) = self.scope.constructors.get(&spelling) {
            return Ok(h::ExprKind::Constructor(constructor));
        }
        Err(error(
            self.module,
            name.0,
            format!("unknown name `{}`", name.text(self.source)),
        ))
    }

    fn static_method(
        &mut self,
        head: &s::Expr,
        member: s::Name,
    ) -> Option<Result<Symbol, ResolveError>> {
        let s::ExprKind::Name(owner) = &head.kind else {
            return None;
        };
        let owner_spelling = self.symbols.intern(owner.text(self.source));
        let binding = self.scope.types.get(&owner_spelling)?;
        let member_spelling = self.symbols.intern(member.text(self.source));
        Some(
            binding
                .methods
                .get(&member_spelling)
                .copied()
                .ok_or_else(|| {
                    error(
                        self.module,
                        member.0,
                        format!(
                            "type `{}` has no method `{}`",
                            owner.text(self.source),
                            member.text(self.source)
                        ),
                    )
                }),
        )
    }
}

fn global_value(
    module: ModuleId,
    name: s::Name,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<Symbol, ResolveError> {
    let spelling = symbols.intern(name.text(source));
    scope.values.get(&spelling).copied().ok_or_else(|| {
        error(
            module,
            name.0,
            format!("unknown value `{}`", name.text(source)),
        )
    })
}

fn method_name(
    module: ModuleId,
    name: s::Name,
    source: &str,
    binding: &TypeBinding,
    symbols: &mut Symbols,
) -> Result<Symbol, ResolveError> {
    let spelling = symbols.intern(name.text(source));
    binding.methods.get(&spelling).copied().ok_or_else(|| {
        error(
            module,
            name.0,
            format!("unknown method `{}`", name.text(source)),
        )
    })
}

fn error(module: ModuleId, span: s::Span, message: impl Into<String>) -> ResolveError {
    ResolveError {
        module,
        span,
        message: message.into(),
    }
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
            let root = std::env::temp_dir().join(format!("faun-resolve-{unique}"));
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

    #[test]
    fn resolves_prelude_types_constructors_and_static_methods() {
        let fixture = Fixture::new();
        fixture.write(
            "nat.fn",
            "exports {Nat.*}\nNat : [Zero Succ(Nat)].(of_nat : Nat -> Nat of_nat(n) -> n)\n",
        );
        fixture.write(
            "int.fn",
            "exports {Int.*}\nInt : [Pos(Nat) NegSucc(Nat)].(of_nat : Nat -> Int of_nat(n) -> Pos(n) neg : Int -> Int neg(i) -> i)\n",
        );
        fixture.write("u8.fn", "exports {U8.*}\nU8 : Nat\n");
        fixture.write(
            "list.fn",
            "exports {List.*}\nList(a) : [Nil Cons(a List(a))]\n",
        );
        fixture.write("str.fn", "exports {Str}\nStr : List(U8)\n");
        let standard = fixture.write(
            "standard.fn",
            "lib {}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8.*}\nimport list {List.*}\nimport str {Str}\nexports {Nat.* Int.* U8.* List.* Str}\n",
        );
        let entry = fixture.write(
            "main.fn",
            "number : Int\nnumber() -> Int.of_nat(42)\ntext : Str\ntext() -> \"é\"\n",
        );
        let loaded = modules::load(&entry, Some(&standard)).unwrap();
        let resolved = resolve(loaded).unwrap();
        let entry = &resolved.program.modules.last().unwrap().items;
        let h::Item::Clause(number) = &entry[1] else {
            panic!("number clause")
        };
        let h::ExprKind::Call(head, arguments) = &number.body.result.kind else {
            panic!("static call")
        };
        assert!(matches!(head.kind, h::ExprKind::Global(_)));
        assert!(matches!(arguments[0].kind, h::ExprKind::Number(_)));
        let h::Item::Clause(text) = &entry[3] else {
            panic!("text clause")
        };
        let h::ExprKind::String(parts) = &text.body.result.kind else {
            panic!("string literal")
        };
        assert_eq!(parts, &[h::StringPart::Text(vec![0xc3, 0xa9])]);
    }

    #[test]
    fn rejects_an_unresolved_name_at_its_span() {
        let fixture = Fixture::new();
        let entry = fixture.write("main.fn", "f() -> missing\n");
        let loaded = modules::load(&entry, None).unwrap();
        let failure = resolve(loaded).unwrap_err();
        let at = failure.location.expect("a place in the source");
        assert_eq!((at.line, at.column, at.width), (1, 8, 7));
    }
}
