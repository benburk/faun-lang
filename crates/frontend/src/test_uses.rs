//! What only expectations may reach: the packages a header names in
//! `test_uses`.
//!
//! A package's test code is its expectations and what only they reach; the
//! rest is real code, what its root exports and its `main!` reach, and any
//! definition that nothing in the package reaches. A name a package imports
//! only from a `test_uses` package is refused in real code, told where real
//! code first reaches the definition that names it, so a test helper can
//! never quietly become a dependency of every package depending on this one.
//!
//! The edges are what a definition names: a global, a constructor, a type,
//! and, since a method is found by its type, every method of the package
//! spelled as a member it asks for. Over-approximating them only widens
//! both test and real code; a name is refused only where it is written.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast::Span;
use crate::context::Context;
use crate::diagnostic::Diagnostic;
use crate::hir as h;
use crate::modules::{Interface, LoadedProgram};
use crate::{ModuleId, Symbol};

/// What the check reads of a loaded program before resolution consumes it.
pub(crate) struct Facts {
    /// Each name only a `test_uses` package gives the entry's package.
    test: HashSet<Symbol>,
    /// The canonical method of the package each spelling may name.
    methods: HashMap<Symbol, Vec<Symbol>>,
    /// What the entry exports, and its `main!`, where it has one.
    roots: Vec<Symbol>,
}

impl Facts {
    pub(crate) fn of(loaded: &LoadedProgram) -> Self {
        let mut test = HashSet::new();
        let mut real = HashSet::new();
        for &(module, is_test) in &loaded.dependencies {
            let names = if is_test { &mut test } else { &mut real };
            names.extend(interface_names(&loaded.module(module).public));
        }
        let mut methods: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        for &id in &loaded.package {
            for binding in loaded.module(id).scope.types.values() {
                for (&spelling, &canonical) in &binding.methods {
                    methods.entry(spelling).or_default().push(canonical);
                }
            }
        }
        let entry = loaded.module(loaded.entry);
        let mut roots: Vec<Symbol> = interface_names(&entry.public).collect();
        let main = format!("{}$$main!", loaded.symbols.text(entry.namespace));
        roots.extend(loaded.symbols.find(&main));
        Self {
            test: test.difference(&real).copied().collect(),
            methods,
            roots,
        }
    }
}

/// Every canonical name `interface` binds.
fn interface_names(interface: &Interface) -> impl Iterator<Item = Symbol> + '_ {
    let values = interface.values.values().copied();
    let types = interface.types.values().flat_map(|binding| {
        std::iter::once(binding.canonical).chain(binding.constructors.values().copied())
    });
    values.chain(types)
}

/// A definition of the package: where it is written and what it names.
struct Definition {
    module: ModuleId,
    names: Vec<Named>,
}

/// A name a definition writes, and where; or, where it is not `written`,
/// one a word it writes may stand for, which only widens what it reaches.
#[derive(Clone, Copy)]
struct Named {
    name: Symbol,
    at: Span,
    written: bool,
}

const fn written(name: Symbol, at: Span) -> Named {
    Named {
        name,
        at,
        written: true,
    }
}

const fn may_be(name: Symbol, at: Span) -> Named {
    Named {
        name,
        at,
        written: false,
    }
}

/// Refuse real code of `program`'s package that names what only a
/// `test_uses` package gives it.
///
/// # Errors
/// Reports the first such definition, in the order the package is written,
/// with the chain real code reaches it by.
pub(crate) fn check(program: &h::Program, cx: &Context, facts: &Facts) -> Result<(), Diagnostic> {
    if facts.test.is_empty() {
        return Ok(());
    }
    let package = Package::of(program, cx);
    let tested = package.reach(&package.expectations, facts);
    let roots: Vec<Symbol> = package
        .order
        .iter()
        .copied()
        .filter(|name| !tested.contains_key(name) || facts.roots.contains(name))
        .collect();
    let real = package.reach(&roots, facts);
    for name in &package.order {
        if !real.contains_key(name) {
            continue;
        }
        let definition = &package.definitions[name];
        if let Some(named) = definition
            .names
            .iter()
            .find(|named| named.written && facts.test.contains(&named.name))
        {
            return Err(refused(cx, &real, *name, definition.module, named));
        }
    }
    Ok(())
}

/// The definitions of a program's package.
struct Package {
    definitions: HashMap<Symbol, Definition>,
    /// Each definition's name, in the order the package writes them.
    order: Vec<Symbol>,
    /// The type each constructor of the package makes.
    owners: HashMap<Symbol, Symbol>,
    expectations: Vec<Symbol>,
}

impl Package {
    fn of(program: &h::Program, cx: &Context) -> Self {
        let mut package = Self {
            definitions: HashMap::new(),
            order: Vec::new(),
            owners: HashMap::new(),
            expectations: Vec::new(),
        };
        for module in &program.modules {
            if !cx.package.contains(&module.source) {
                continue;
            }
            package
                .expectations
                .extend(module.expectations.iter().copied());
            for item in &module.items {
                item_names(
                    item,
                    module.source,
                    &mut package.definitions,
                    &mut package.order,
                    &mut package.owners,
                );
            }
        }
        package
    }

    /// The definitions `definition` reaches.
    fn edges(&self, definition: &Definition, facts: &Facts) -> Vec<Symbol> {
        let mut next = Vec::new();
        for named in &definition.names {
            next.push(self.owners.get(&named.name).copied().unwrap_or(named.name));
            next.extend(
                facts
                    .methods
                    .get(&named.name)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        next.retain(|name| self.definitions.contains_key(name));
        next
    }

    /// What `roots` reach, each with the definition it was first reached
    /// from, none for a root.
    fn reach(&self, roots: &[Symbol], facts: &Facts) -> HashMap<Symbol, Option<Symbol>> {
        let mut parents = HashMap::new();
        let mut queue = VecDeque::new();
        for &root in roots {
            if self.definitions.contains_key(&root)
                && let Entry::Vacant(entry) = parents.entry(root)
            {
                entry.insert(None);
                queue.push_back(root);
            }
        }
        while let Some(name) = queue.pop_front() {
            for next in self.edges(&self.definitions[&name], facts) {
                if let Entry::Vacant(entry) = parents.entry(next) {
                    entry.insert(Some(name));
                    queue.push_back(next);
                }
            }
        }
        parents
    }
}

/// The refusal of `name`, which real code reaches by `parents`, for naming
/// `used`, a test dependency's, in `module`.
fn refused(
    cx: &Context,
    parents: &HashMap<Symbol, Option<Symbol>>,
    name: Symbol,
    module: ModuleId,
    used: &Named,
) -> Diagnostic {
    let spelled = |name: Symbol| format!("`{}`", cx.symbols.spelling(name));
    let mut chain = vec![spelled(name)];
    let mut reached = name;
    while let Some(&Some(parent)) = parents.get(&reached) {
        chain.push(spelled(parent));
        reached = parent;
    }
    let at = used.at;
    let used = spelled(used.name);
    let mut diagnostic = cx
        .diagnostic(
            module,
            at,
            format!("{used} is from a test dependency, and real code uses it"),
        )
        .label(format!("{} uses it", chain[0]))
        .note("only expectations, and what only they reach, may use a package in `test_uses`");
    if chain.len() > 1 {
        let calls: Vec<&str> = chain.iter().rev().map(String::as_str).collect();
        diagnostic = diagnostic.note(format!("real code reaches it: {}", calls.join(" calls ")));
    }
    diagnostic.help(format!(
        "move the package {used} comes from to `uses`, or keep {} out of real code",
        chain[0]
    ))
}

/// Record what `item` defines and names.
fn item_names(
    item: &h::Item,
    module: ModuleId,
    definitions: &mut HashMap<Symbol, Definition>,
    order: &mut Vec<Symbol>,
    owners: &mut HashMap<Symbol, Symbol>,
) {
    let mut define = |name: Symbol, names: Vec<Named>| {
        let definition = definitions.entry(name).or_insert_with(|| {
            order.push(name);
            Definition {
                module,
                names: Vec::new(),
            }
        });
        definition.names.extend(names);
    };
    match item {
        h::Item::Data(data) => {
            let mut names = Vec::new();
            for constructor in &data.constructors {
                owners.insert(constructor.name, data.name);
                for field in &constructor.fields {
                    type_names(field, data.span, &mut names);
                }
            }
            if let Some(wrapper) = &data.wrapper {
                owners.insert(wrapper.constructor, data.name);
                type_names(&wrapper.field, data.span, &mut names);
            }
            define(data.name, names);
            for method in &data.methods {
                match method {
                    h::MethodItem::Signature(signature) => {
                        define(signature.name, signature_names(signature));
                    }
                    h::MethodItem::Clause(clause) => {
                        define(clause.name, clause_names(clause));
                    }
                }
            }
        }
        h::Item::Signature(signature) => {
            define(signature.name, signature_names(signature));
        }
        h::Item::Clause(clause) => define(clause.name, clause_names(clause)),
    }
}

fn signature_names(signature: &h::SignatureDecl) -> Vec<Named> {
    let mut names = Vec::new();
    for ty in signature.parameters.iter().chain([&signature.result]) {
        type_names(ty, signature.span, &mut names);
    }
    for constraint in &signature.constraints {
        match constraint {
            h::Constraint::Member { ty, .. } => type_names(ty, signature.span, &mut names),
            h::Constraint::Alias { arguments, .. } => {
                for ty in arguments {
                    type_names(ty, signature.span, &mut names);
                }
            }
        }
    }
    names
}

fn type_names(ty: &h::Type, span: Span, names: &mut Vec<Named>) {
    match ty {
        h::Type::Named(name, arguments) => {
            names.push(written(*name, span));
            for argument in arguments {
                type_names(argument, span, names);
            }
        }
        h::Type::Function(parameters, result) => {
            for parameter in parameters {
                type_names(parameter, span, names);
            }
            type_names(result, span, names);
        }
        h::Type::Variants(constructors) => {
            for field in constructors
                .iter()
                .flat_map(|constructor| &constructor.fields)
            {
                type_names(field, span, names);
            }
        }
        h::Type::Record(fields, _) => {
            for (_, field) in fields {
                type_names(field, span, names);
            }
        }
        h::Type::Tuple(elements) => {
            for element in elements {
                type_names(element, span, names);
            }
        }
        h::Type::Variable(_) | h::Type::Hole => {}
    }
}

fn clause_names(clause: &h::Clause) -> Vec<Named> {
    let mut names = Vec::new();
    for pattern in &clause.patterns {
        pattern_names(pattern, clause.span, &mut names);
    }
    if let Some(guard) = &clause.guard {
        expr_names(guard, &mut names);
    }
    body_names(&clause.body, &mut names);
    names
}

fn body_names(body: &h::Body, names: &mut Vec<Named>) {
    for binding in &body.bindings {
        pattern_names(&binding.pattern, binding.value.span, names);
    }
    for expression in body.exprs() {
        expr_names(expression, names);
    }
}

fn expr_names(expression: &h::Expr, names: &mut Vec<Named>) {
    let span = expression.span;
    match &expression.kind {
        h::ExprKind::Global(name) | h::ExprKind::Constructor(name) => {
            names.push(written(*name, span));
        }
        h::ExprKind::Dual(dual) => {
            names.extend(dual.candidates.iter().map(|&name| may_be(name, span)));
        }
        h::ExprKind::Method(_, member, at, _) => names.push(may_be(*member, *at)),
        h::ExprKind::Member(_, member) => names.push(may_be(*member, span)),
        h::ExprKind::Lambda(patterns, _) => {
            for pattern in patterns {
                pattern_names(pattern, span, names);
            }
        }
        h::ExprKind::Is(_, pattern) => pattern_names(pattern, span, names),
        h::ExprKind::Match(_, arms) => {
            for arm in arms {
                pattern_names(&arm.pattern, span, names);
            }
        }
        h::ExprKind::Block(body) => {
            for binding in &body.bindings {
                pattern_names(&binding.pattern, span, names);
            }
        }
        _ => {}
    }
    expression.for_each_child(|inner| expr_names(inner, names));
}

fn pattern_names(pattern: &h::Pattern, span: Span, names: &mut Vec<Named>) {
    let inner: &[h::Pattern] = match pattern {
        h::Pattern::Constructor(name, inner) => {
            names.push(written(*name, span));
            inner
        }
        h::Pattern::Dual(dual, inner) => {
            names.extend(dual.candidates.iter().map(|&name| may_be(name, span)));
            inner
        }
        h::Pattern::Tag(_, inner) | h::Pattern::Tuple(inner) | h::Pattern::Or(inner) => inner,
        h::Pattern::List(elements, rest) => {
            if let Some(rest) = rest {
                pattern_names(rest, span, names);
            }
            elements
        }
        h::Pattern::Ending(front, elements) => {
            pattern_names(front, span, names);
            elements
        }
        h::Pattern::Record(fields, _) => {
            for (_, field) in fields {
                pattern_names(field, span, names);
            }
            &[]
        }
        h::Pattern::As(_, inner) => {
            pattern_names(inner, span, names);
            &[]
        }
        h::Pattern::Wild
        | h::Pattern::Bind(_)
        | h::Pattern::Number { .. }
        | h::Pattern::Range(..)
        | h::Pattern::String(_) => &[],
    };
    for pattern in inner {
        pattern_names(pattern, span, names);
    }
}
