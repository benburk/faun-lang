//! Group signatures and clauses once, lifting methods into the function table.
//!
//! This is still unchecked syntax: a signature may be absent, and checking must
//! compare every clause's arity. Data declarations contain only type templates;
//! their methods are ordinary functions with an owner, not nested declarations.

use std::collections::{HashMap, HashSet};

use crate::ast::Span;
use crate::hir as h;
use crate::resolve::ResolvedProgram;
use crate::{ModuleId, Symbol};

#[derive(Clone, Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub data: HashMap<Symbol, Data>,
    pub visible_methods: HashMap<ModuleId, HashSet<Symbol>>,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub module: ModuleId,
    pub name: Symbol,
    pub owner: Option<Symbol>,
    pub signature: Option<h::SignatureDecl>,
    pub clauses: Vec<h::Clause>,
}

#[derive(Clone, Debug)]
pub struct Data {
    pub module: ModuleId,
    pub span: Span,
    pub name: Symbol,
    pub parameters: Vec<Symbol>,
    pub constructors: Vec<h::ConstructorDecl>,
    pub wrapper: Option<h::WrapperDecl>,
}

/// Consume module item lists into one declaration per function and type.
#[must_use]
#[allow(clippy::too_many_lines)] // Keep the declaration walk exhaustive in one place.
pub fn normalize(resolved: ResolvedProgram) -> ResolvedProgram<Program> {
    resolved.map(|program, _| {
        let mut output = Program {
            functions: Vec::new(),
            data: HashMap::new(),
            visible_methods: HashMap::new(),
        };
        let mut indices = HashMap::new();
        for module in program.modules {
            output
                .visible_methods
                .insert(module.source, module.visible_methods.into_iter().collect());
            for item in module.items {
                match item {
                    h::Item::Data(data) => {
                        for method in data.methods {
                            let item = match method {
                                h::MethodItem::Signature(signature) => {
                                    h::Item::Signature(signature)
                                }
                                h::MethodItem::Clause(clause) => h::Item::Clause(clause),
                            };
                            output.function(module.source, Some(data.name), item, &mut indices);
                        }
                        output.data.insert(
                            data.name,
                            Data {
                                module: module.source,
                                span: data.span,
                                name: data.name,
                                parameters: data.parameters,
                                constructors: data.constructors,
                                wrapper: data.wrapper,
                            },
                        );
                    }
                    item => output.function(module.source, None, item, &mut indices),
                }
            }
        }
        output
    })
}

impl Program {
    fn function(
        &mut self,
        module: ModuleId,
        owner: Option<Symbol>,
        item: h::Item,
        indices: &mut HashMap<Symbol, usize>,
    ) {
        let name = match &item {
            h::Item::Signature(signature) => signature.name,
            h::Item::Clause(clause) => clause.name,
            h::Item::Data(_) => unreachable!("data's methods are collected separately"),
        };
        let index = *indices.entry(name).or_insert_with(|| {
            let index = self.functions.len();
            self.functions.push(Function {
                module,
                name,
                owner,
                signature: None,
                clauses: Vec::new(),
            });
            index
        });
        let function = &mut self.functions[index];
        match item {
            h::Item::Signature(signature) => function.signature = Some(signature),
            h::Item::Clause(clause) => function.clauses.push(clause),
            h::Item::Data(_) => unreachable!("data's methods are collected separately"),
        }
    }
}
