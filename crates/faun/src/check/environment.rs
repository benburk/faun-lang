//! What a program's declarations tell inference before any clause is
//! read: each declared type's constructors and fields, each signature as a
//! scheme with its bounds, and each method written without one.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::unify::{Infer, Scheme, Tags, Ty, free_variables};
use super::{
    Bound, Checker, Facts, FieldImpl, MethodImpl, UnsignedMethod, failure, first_order, has_hole,
    passable,
};
use crate::blessed::PreludeIds;
use crate::declarations as n;
use crate::diagnostic::{Advised, Refusal};
use crate::hir as h;
use crate::{ModuleId, Symbol, Symbols};

impl<'a> Checker<'a> {
    pub(super) fn new(
        program: &'a n::Program,
        symbols: &'a Symbols,
        prelude: &'a PreludeIds,
    ) -> Result<Self, Refusal> {
        let mut checker = Self {
            symbols,
            prelude,
            infer: Infer::default(),
            values: HashMap::new(),
            open: HashSet::new(),
            constructors: HashMap::new(),
            methods: HashMap::new(),
            fields: HashMap::new(),
            visible_methods: &program.visible_methods,
            pending_methods: Vec::new(),
            obliging: None,
            pending_numerals: Vec::new(),
            pending_tags: Vec::new(),
            pending_bare: Vec::new(),
            pending_closings: Vec::new(),
            joins: Vec::new(),
            pending_ways: Vec::new(),
            answers: Vec::new(),
            written_result: None,
            clause_marks: None,
            merges: HashMap::new(),
            prefix_helps: HashMap::new(),
            loops: Vec::new(),
            bounds: HashMap::new(),
            variable_names: HashMap::new(),
            partial: HashMap::new(),
            current: Vec::new(),
            current_names: HashMap::new(),
            bound_sites: Vec::new(),
            expression_types: Vec::new(),
            handings: Vec::new(),
            clause_types: Vec::new(),
            widenings: Vec::new(),
            checked: Facts::default(),
        };
        for data in program.data.values() {
            checker.add_data(data.module, data)?;
        }
        for function in &program.functions {
            if let Some(signature) = &function.signature {
                checker.add_signature(function.module, signature, function.owner)?;
            }
        }
        checker.validate_literal_protocols(program)?;
        Ok(checker)
    }

    fn add_data(&mut self, module: ModuleId, data: &n::Data) -> Result<(), Refusal> {
        let written = data
            .constructors
            .iter()
            .map(|constructor| (constructor.name, constructor.fields.as_slice()))
            .chain(
                data.wrapper
                    .iter()
                    .map(|wrapper| (wrapper.constructor, std::slice::from_ref(&wrapper.field))),
            );
        for (constructor, fields) in written {
            if !fields.iter().all(first_order) {
                let message = format!(
                    "constructor `{}` holds a function",
                    self.symbols.spelling(constructor)
                );
                return Err(failure(module, data.span, message)
                    .note("data may not store functions; a function is passed into a call"));
            }
        }
        let mut variables = HashMap::new();
        for parameter in &data.parameters {
            let fresh = self.infer.fresh();
            variables.insert(*parameter, fresh);
        }
        let arguments: Vec<_> = data
            .parameters
            .iter()
            .map(|parameter| variables[parameter].clone())
            .collect();
        let result = Ty::Named(data.name, arguments.into());
        for constructor in &data.constructors {
            let fields: Vec<_> = constructor
                .fields
                .iter()
                .map(|field| self.surface_type(field, &mut variables))
                .collect();
            let ty = if fields.is_empty() {
                result.clone()
            } else {
                Ty::Function(fields.into(), Rc::new(result.clone()))
            };
            self.constructors.insert(
                constructor.name,
                Scheme {
                    variables: free_variables(&ty),
                    ty,
                },
            );
        }
        if let Some(wrapper) = &data.wrapper {
            let field = self.surface_type(&wrapper.field, &mut variables);
            if matches!(&field, Ty::Record(_, Some(_))) {
                return Err(
                    failure(module, data.span, "a declared type's record is closed")
                        .help("write a record with `*` where it is taken, in a signature"),
                );
            }
            if let Ty::Record(fields, _) = &field {
                for (name, field_ty) in fields.iter() {
                    let ty = Ty::Function(Rc::from([result.clone()]), Rc::new(field_ty.clone()));
                    self.fields.entry(*name).or_default().push(FieldImpl {
                        owner: data.name,
                        scheme: Scheme {
                            variables: free_variables(&ty),
                            ty,
                        },
                    });
                }
            }
            let ty = Ty::Function(Rc::from([field]), Rc::new(result));
            self.constructors.insert(
                wrapper.constructor,
                Scheme {
                    variables: free_variables(&ty),
                    ty,
                },
            );
        }
        Ok(())
    }

    fn add_signature(
        &mut self,
        module: ModuleId,
        signature: &h::SignatureDecl,
        owner: Option<Symbol>,
    ) -> Result<(), Refusal> {
        // A function is passed into a call, so it is a parameter's type,
        // never an answer's or data's.
        if !first_order(&signature.result) || !signature.parameters.iter().all(passable) {
            let message = format!(
                "`{}` holds a function other than as a parameter",
                self.symbols.text(signature.spelling)
            );
            return Err(failure(module, signature.span, message)
                .note("a function is passed into a call, never answered or stored"));
        }
        if signature
            .parameters
            .iter()
            .chain([&signature.result])
            .any(has_hole)
        {
            if !signature.constraints.is_empty() {
                let note = format!(
                    "`{}` writes `_`, so its type is worked out from its clauses",
                    self.symbols.text(signature.spelling)
                );
                let message = "a signature that writes `_` takes no `where` bounds";
                return Err(failure(module, signature.span, message).note(note));
            }
            self.partial.insert(signature.name, signature.clone());
            return Ok(());
        }
        let mut variables = HashMap::new();
        let ty = self.signed_type(signature, &mut variables);
        let ty = self.open_result_rows(&ty, true);
        let bounds = self.written_bounds(module, signature, &mut variables)?;
        let mut quantified = free_variables(&ty);
        for bound in &bounds {
            for variable in free_variables(&bound.ty) {
                if !quantified.contains(&variable) {
                    quantified.push(variable);
                }
            }
        }
        let scheme = Scheme {
            variables: quantified,
            ty,
        };
        self.set_value(signature.name, scheme.clone());
        self.bounds.insert(signature.name, bounds);
        self.variable_names.insert(
            signature.name,
            variables
                .iter()
                .filter_map(|(name, ty)| match ty {
                    Ty::Var(variable) => Some((*name, *variable)),
                    _ => None,
                })
                .collect(),
        );
        if let Some(owner) = owner {
            self.methods
                .entry(signature.spelling)
                .or_default()
                .push(MethodImpl {
                    owner,
                    target: signature.name,
                    scheme,
                    bound: false,
                });
        }
        Ok(())
    }

    /// The function type `signature` writes, over `variables`.
    pub(super) fn signed_type(
        &mut self,
        signature: &h::SignatureDecl,
        variables: &mut HashMap<Symbol, Ty>,
    ) -> Ty {
        let parameters = signature
            .parameters
            .iter()
            .map(|ty| self.surface_type(ty, variables))
            .collect();
        let result = self.surface_type(&signature.result, variables);
        Ty::Function(parameters, Rc::new(result))
    }

    /// The methods a type's block defines without a signature, by the
    /// spelling a dot calls them by.
    pub(super) fn unsigned_methods(
        &self,
        program: &n::Program,
        unsigned: &HashSet<Symbol>,
    ) -> HashMap<Symbol, Vec<UnsignedMethod>> {
        let mut methods: HashMap<Symbol, Vec<UnsignedMethod>> = HashMap::new();
        for function in &program.functions {
            let Some(owner) = function.owner else {
                continue;
            };
            if !unsigned.contains(&function.name) {
                continue;
            }
            let canonical = self.symbols.text(function.name);
            let Some(spelling) = canonical
                .rsplit_once('.')
                .and_then(|(_, spelled)| self.symbols.find(spelled))
            else {
                continue;
            };
            methods.entry(spelling).or_default().push(UnsignedMethod {
                name: function.name,
                owner,
            });
        }
        methods
    }

    /// `name`, where it is a method written without a signature, callable
    /// with a dot at `scheme`: its type while its own component is being
    /// worked out, and what that settled on after.
    pub(super) fn register_unsigned(
        &mut self,
        methods: &HashMap<Symbol, Vec<UnsignedMethod>>,
        name: Symbol,
        scheme: Scheme,
    ) {
        let Some((&spelling, method)) = methods.iter().find_map(|(spelling, methods)| {
            methods
                .iter()
                .find(|method| method.name == name)
                .map(|method| (spelling, method))
        }) else {
            return;
        };
        let implementations = self.methods.entry(spelling).or_default();
        implementations.retain(|implementation| implementation.target != name);
        implementations.push(MethodImpl {
            owner: method.owner,
            target: name,
            scheme,
            bound: false,
        });
    }

    /// A signature's `where` bounds, over its own type variables. A
    /// variable a bound alone mentions is quantified too: which type it is,
    /// the bound's implementation says at each specialization. A bound may
    /// be on such a variable, one a bound on a variable already determined
    /// mentions, since that bound's implementation determines it in turn;
    /// on any other, it could never be met, and is refused.
    fn written_bounds(
        &mut self,
        module: ModuleId,
        signature: &h::SignatureDecl,
        variables: &mut HashMap<Symbol, Ty>,
    ) -> Result<Vec<Bound>, Refusal> {
        let mut bounds: Vec<Option<Bound>> = vec![None; signature.constraints.len()];
        loop {
            let mut progress = false;
            for (constraint, bound) in signature.constraints.iter().zip(&mut bounds) {
                let (variable, member, ty, through) = match constraint {
                    h::Constraint::Member {
                        variable,
                        member,
                        ty,
                        through,
                    } => (*variable, *member, ty, *through),
                    h::Constraint::Alias { .. } => {
                        unreachable!("resolution expands every constraint alias")
                    }
                };
                if bound.is_some() {
                    continue;
                }
                let Some(owner) = variables.get(&variable).cloned() else {
                    continue;
                };
                let ty = self.surface_type(ty, variables);
                // A member taking the type first is a method of its values;
                // anything else is reached through the type.
                let associated = !matches!(&ty, Ty::Function(parameters, _)
                    if parameters.first().is_some_and(|first| *first == owner));
                *bound = Some(Bound {
                    owner,
                    member,
                    ty,
                    associated,
                    bare: false,
                    through,
                    numeral: false,
                });
                progress = true;
            }
            if !progress {
                break;
            }
        }
        if let Some(h::Constraint::Member { variable, .. }) = signature
            .constraints
            .iter()
            .zip(&bounds)
            .find_map(|(constraint, bound)| bound.is_none().then_some(constraint))
        {
            return Err(failure(
                module,
                signature.span,
                format!(
                    "`where` bounds `{}`, which neither the signature nor another bound determines",
                    self.symbols.text(*variable)
                ),
            ));
        }
        Ok(bounds.into_iter().flatten().collect())
    }

    /// Give every nonempty tag row in result position a tail, which the
    /// scheme then quantifies.
    ///
    /// A signature's `Result(a, [Empty])` says what this definition fails
    /// with, and its body is checked against exactly that: skolemized, the
    /// tail is rigid, so a body answering another tag is refused. It says
    /// nothing about callers, whose business it is whether `Empty` travels
    /// in one row with their own failures: instantiated, the tail is a
    /// variable they may widen. A row in a parameter is what a definition
    /// handles, and stays closed. The empty row is the type with no values
    /// rather than a failure row, and stays closed too.
    fn open_result_rows(&mut self, ty: &Ty, positive: bool) -> Ty {
        match ty {
            Ty::Var(_) | Ty::Rigid(_) => ty.clone(),
            Ty::Named(name, arguments) => Ty::Named(
                *name,
                arguments
                    .iter()
                    .map(|ty| self.open_result_rows(ty, positive))
                    .collect(),
            ),
            Ty::Function(parameters, result) => Ty::Function(
                parameters
                    .iter()
                    .map(|ty| self.open_result_rows(ty, !positive))
                    .collect(),
                Rc::new(self.open_result_rows(result, positive)),
            ),
            Ty::Variants(tags, tail) => {
                let tags: Tags = tags
                    .iter()
                    .map(|(name, fields)| {
                        let fields = fields
                            .iter()
                            .map(|ty| self.open_result_rows(ty, positive))
                            .collect();
                        (*name, fields)
                    })
                    .collect();
                let tail = match tail {
                    None if positive && !tags.is_empty() => Some(Rc::new(self.infer.fresh())),
                    other => other.clone(),
                };
                Ty::Variants(tags.into(), tail)
            }
            Ty::Record(fields, tail) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.open_result_rows(ty, positive)))
                    .collect(),
                tail.clone(),
            ),
            Ty::Tuple(members) => Ty::Tuple(
                members
                    .iter()
                    .map(|ty| self.open_result_rows(ty, positive))
                    .collect(),
            ),
        }
    }

    fn surface_type(&mut self, ty: &h::Type, variables: &mut HashMap<Symbol, Ty>) -> Ty {
        match ty {
            h::Type::Named(name, arguments) => Ty::Named(
                *name,
                arguments
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
            ),
            h::Type::Variable(name) => variables
                .entry(*name)
                .or_insert_with(|| self.infer.fresh())
                .clone(),
            // Whatever the clauses make it: a variable no scheme quantifies
            // until they have.
            h::Type::Hole => self.infer.fresh(),
            h::Type::Function(parameters, result) => Ty::Function(
                parameters
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
                Rc::new(self.surface_type(result, variables)),
            ),
            // A written row is closed: it is exactly these tags.
            h::Type::Variants(constructors) => Ty::Variants(
                constructors
                    .iter()
                    .map(|constructor| {
                        (
                            constructor.name,
                            constructor
                                .fields
                                .iter()
                                .map(|ty| self.surface_type(ty, variables))
                                .collect(),
                        )
                    })
                    .collect(),
                None,
            ),
            // `*` stands for whatever other fields a caller's record has:
            // a tail of its own, which the scheme quantifies.
            h::Type::Record(fields, open) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, self.surface_type(ty, variables)))
                    .collect(),
                open.then(|| Rc::new(self.infer.fresh())),
            ),
            h::Type::Tuple(members) => Ty::Tuple(
                members
                    .iter()
                    .map(|ty| self.surface_type(ty, variables))
                    .collect(),
            ),
        }
    }

    fn validate_literal_protocols(&self, program: &n::Program) -> Result<(), Refusal> {
        let Some(module) = program.functions.first().map(|function| function.module) else {
            return Ok(());
        };
        for (function, parameters, result, written) in [
            (
                self.prelude.int_of_nat,
                vec![self.prelude.nat],
                self.prelude.int,
                "Int.of_nat : Nat -> Int",
            ),
            (
                self.prelude.int_neg,
                vec![self.prelude.int],
                self.prelude.int,
                "Int.neg : Int -> Int",
            ),
        ] {
            let Some(scheme) = self.values.get(&function) else {
                return Err(failure(
                    module,
                    crate::ast::Span::default(),
                    format!("the prelude must define `{written}` for integer literals"),
                ));
            };
            let expected = Ty::Function(
                parameters
                    .into_iter()
                    .map(|name| Ty::Named(name, Rc::default()))
                    .collect(),
                Rc::new(Ty::Named(result, Rc::default())),
            );
            if scheme.ty != expected {
                return Err(failure(
                    module,
                    crate::ast::Span::default(),
                    format!("the prelude must define `{written}` for integer literals"),
                ));
            }
        }
        Ok(())
    }
}
