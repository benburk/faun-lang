//! Signature-directed checking for the first frontend slice.
//!
//! This is intentionally smaller than full inference: explicit function and
//! constructor signatures provide expected types, while unconstrained positive
//! numerals default to `Nat` and directly negative ones to `Int`. The output
//! records fully elaborated literals so later lowering never guesses from a
//! spelling.

// Exhaustive pattern and expression checks are easier to audit together than
// split across forwarding helpers to meet a line-count heuristic.
#![allow(clippy::too_many_lines)]

use std::collections::HashMap;
use std::fmt;

use super::blessed::{self, LiteralExpr, NumeralType, PreludeIds};
use super::hir as h;
use super::{ModuleId, Symbol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralSite {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub ty: Symbol,
    pub value: LiteralExpr,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckedLiterals {
    pub sites: Vec<LiteralSite>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub module: ModuleId,
    pub span: super::ast::Span,
    pub message: String,
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CheckError {}

#[derive(Default)]
struct Environment {
    functions: HashMap<Symbol, h::Type>,
    constructors: HashMap<Symbol, h::Type>,
}

/// Check the explicitly signed first-order slice and elaborate its literals.
///
/// Clauses without signatures still have their literals checked using local
/// context and defaults; broader Hindley–Milner inference remains a later pass.
///
/// # Errors
///
/// Reports arity, direct type mismatches, negative `Nat` literals, and literals
/// used where neither `Nat`, `Int`, nor `Str` is expected.
pub fn literals(program: &h::Program, prelude: &PreludeIds) -> Result<CheckedLiterals, CheckError> {
    let environment = environment(program);
    validate_literal_protocols(program, &environment, prelude)?;
    let mut checked = CheckedLiterals::default();
    for module in &program.modules {
        for item in &module.items {
            match item {
                h::Item::Clause(clause) => {
                    check_clause(module.source, clause, &environment, prelude, &mut checked)?;
                }
                h::Item::Data(data) => {
                    for method in &data.methods {
                        if let h::MethodItem::Clause(clause) = method {
                            check_clause(
                                module.source,
                                clause,
                                &environment,
                                prelude,
                                &mut checked,
                            )?;
                        }
                    }
                }
                h::Item::Signature(_) => {}
            }
        }
    }
    Ok(checked)
}

fn environment(program: &h::Program) -> Environment {
    let mut environment = Environment::default();
    for module in &program.modules {
        for item in &module.items {
            match item {
                h::Item::Signature(signature) => {
                    environment.functions.insert(
                        signature.name,
                        h::Type::Function(
                            signature.parameters.clone(),
                            Box::new(signature.result.clone()),
                        ),
                    );
                }
                h::Item::Data(data) => {
                    let result = h::Type::Named(
                        data.name,
                        data.parameters
                            .iter()
                            .copied()
                            .map(h::Type::Variable)
                            .collect(),
                    );
                    for constructor in &data.constructors {
                        environment.constructors.insert(
                            constructor.name,
                            h::Type::Function(constructor.fields.clone(), Box::new(result.clone())),
                        );
                    }
                    for method in &data.methods {
                        if let h::MethodItem::Signature(signature) = method {
                            environment.functions.insert(
                                signature.name,
                                h::Type::Function(
                                    signature.parameters.clone(),
                                    Box::new(signature.result.clone()),
                                ),
                            );
                        }
                    }
                }
                h::Item::Clause(_) => {}
            }
        }
    }
    environment
}

fn validate_literal_protocols(
    program: &h::Program,
    environment: &Environment,
    prelude: &PreludeIds,
) -> Result<(), CheckError> {
    let Some(module) = program.modules.first().map(|module| module.source) else {
        return Ok(());
    };
    let nat = named(prelude.nat);
    let int = named(prelude.int);
    for (function, expected, name) in [
        (
            prelude.int_of_nat,
            h::Type::Function(vec![nat], Box::new(int.clone())),
            "Int.of_nat : Nat -> Int",
        ),
        (
            prelude.int_neg,
            h::Type::Function(vec![int.clone()], Box::new(int)),
            "Int.neg : Int -> Int",
        ),
    ] {
        if environment.functions.get(&function) != Some(&expected) {
            return Err(failure(
                module,
                super::ast::Span::default(),
                format!("the prelude must define `{name}` for integer literals"),
            ));
        }
    }
    Ok(())
}

fn check_clause(
    module: ModuleId,
    clause: &h::Clause,
    environment: &Environment,
    prelude: &PreludeIds,
    checked: &mut CheckedLiterals,
) -> Result<(), CheckError> {
    let signature = environment.functions.get(&clause.name);
    let (parameters, result) = match signature {
        Some(h::Type::Function(parameters, result)) => {
            (parameters.as_slice(), Some(result.as_ref()))
        }
        _ => (&[][..], None),
    };
    if signature.is_some() && parameters.len() != clause.patterns.len() {
        return Err(failure(
            module,
            clause.span,
            format!(
                "clause takes {} patterns but its signature takes {} parameters",
                clause.patterns.len(),
                parameters.len()
            ),
        ));
    }
    let mut locals = HashMap::new();
    for (index, pattern) in clause.patterns.iter().enumerate() {
        bind_pattern(
            module,
            pattern,
            parameters.get(index),
            environment,
            prelude,
            &mut locals,
            checked,
            clause.span,
        )?;
    }
    if let Some(guard) = &clause.guard {
        infer_expr(module, guard, None, environment, prelude, &locals, checked)?;
    }
    for binding in &clause.body.bindings {
        let value_type = infer_expr(
            module,
            &binding.value,
            None,
            environment,
            prelude,
            &locals,
            checked,
        )?;
        bind_pattern(
            module,
            &binding.pattern,
            value_type.as_ref(),
            environment,
            prelude,
            &mut locals,
            checked,
            binding.value.span,
        )?;
    }
    infer_expr(
        module,
        &clause.body.result,
        result,
        environment,
        prelude,
        &locals,
        checked,
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn bind_pattern(
    module: ModuleId,
    pattern: &h::Pattern,
    expected: Option<&h::Type>,
    environment: &Environment,
    prelude: &PreludeIds,
    locals: &mut HashMap<h::LocalId, h::Type>,
    checked: &mut CheckedLiterals,
    span: super::ast::Span,
) -> Result<(), CheckError> {
    match pattern {
        h::Pattern::Wild => Ok(()),
        h::Pattern::Bind(local) => {
            if let Some(expected) = expected {
                locals.insert(*local, expected.clone());
            }
            Ok(())
        }
        h::Pattern::Constructor(constructor, fields) => {
            let Some(h::Type::Function(parameters, result)) =
                environment.constructors.get(constructor)
            else {
                return Err(failure(module, span, "constructor has no declared type"));
            };
            if fields.len() != parameters.len() {
                return Err(failure(
                    module,
                    span,
                    "constructor pattern has the wrong number of fields",
                ));
            }
            if let Some(expected) = expected {
                ensure_same(module, span, result, expected)?;
            }
            for (field, ty) in fields.iter().zip(parameters) {
                bind_pattern(
                    module,
                    field,
                    Some(ty),
                    environment,
                    prelude,
                    locals,
                    checked,
                    span,
                )?;
            }
            Ok(())
        }
        h::Pattern::Number {
            magnitude,
            negative,
        } => {
            let ty = numeral_type(module, span, expected, *negative, prelude)?;
            checked.sites.push(LiteralSite {
                module,
                span,
                ty: type_symbol(ty, prelude),
                value: elaborate_numeral(module, span, magnitude.clone(), *negative, ty, prelude)?,
            });
            Ok(())
        }
        h::Pattern::Range(start, end) => {
            let ty = numeral_type(module, span, expected, false, prelude)?;
            for magnitude in [start, end] {
                checked.sites.push(LiteralSite {
                    module,
                    span,
                    ty: type_symbol(ty, prelude),
                    value: elaborate_numeral(module, span, magnitude.clone(), false, ty, prelude)?,
                });
            }
            Ok(())
        }
        h::Pattern::List(elements, rest) => {
            for element in elements {
                bind_pattern(
                    module,
                    element,
                    None,
                    environment,
                    prelude,
                    locals,
                    checked,
                    span,
                )?;
            }
            if let Some(rest) = rest {
                bind_pattern(
                    module,
                    rest,
                    expected,
                    environment,
                    prelude,
                    locals,
                    checked,
                    span,
                )?;
            }
            Ok(())
        }
    }
}

fn infer_expr(
    module: ModuleId,
    expression: &h::Expr,
    expected: Option<&h::Type>,
    environment: &Environment,
    prelude: &PreludeIds,
    locals: &HashMap<h::LocalId, h::Type>,
    checked: &mut CheckedLiterals,
) -> Result<Option<h::Type>, CheckError> {
    let inferred = match &expression.kind {
        h::ExprKind::Local(local) => locals.get(local).cloned(),
        h::ExprKind::Global(global) => environment.functions.get(global).cloned(),
        h::ExprKind::Constructor(constructor) => {
            environment
                .constructors
                .get(constructor)
                .map(|ty| match ty {
                    h::Type::Function(parameters, result) if parameters.is_empty() => {
                        result.as_ref().clone()
                    }
                    _ => ty.clone(),
                })
        }
        h::ExprKind::Number(magnitude) => {
            let ty = numeral_type(module, expression.span, expected, false, prelude)?;
            checked.sites.push(LiteralSite {
                module,
                span: expression.span,
                ty: type_symbol(ty, prelude),
                value: elaborate_numeral(
                    module,
                    expression.span,
                    magnitude.clone(),
                    false,
                    ty,
                    prelude,
                )?,
            });
            Some(named(type_symbol(ty, prelude)))
        }
        h::ExprKind::String(parts) => {
            if let Some(expected) = expected {
                ensure_same(module, expression.span, expected, &named(prelude.str_))?;
            }
            let mut bytes = Vec::new();
            let mut interpolated = false;
            for part in parts {
                match part {
                    h::StringPart::Text(text) => bytes.extend_from_slice(text),
                    h::StringPart::Splice(splice) => {
                        interpolated = true;
                        infer_expr(module, splice, None, environment, prelude, locals, checked)?;
                    }
                }
            }
            if !interpolated {
                checked.sites.push(LiteralSite {
                    module,
                    span: expression.span,
                    ty: prelude.str_,
                    value: blessed::string(&bytes, prelude),
                });
            }
            Some(named(prelude.str_))
        }
        h::ExprKind::Call(head, arguments) => {
            let head_type = infer_expr(module, head, None, environment, prelude, locals, checked)?;
            let Some(h::Type::Function(parameters, result)) = head_type else {
                return Err(failure(
                    module,
                    expression.span,
                    "called value is not a function",
                ));
            };
            if parameters.len() != arguments.len() {
                return Err(failure(
                    module,
                    expression.span,
                    format!(
                        "call passes {} arguments to a function taking {}",
                        arguments.len(),
                        parameters.len()
                    ),
                ));
            }
            for (argument, parameter) in arguments.iter().zip(&parameters) {
                infer_expr(
                    module,
                    argument,
                    Some(parameter),
                    environment,
                    prelude,
                    locals,
                    checked,
                )?;
            }
            Some(*result)
        }
        h::ExprKind::Unary(super::ast::UnaryOp::Negate, value)
            if let h::ExprKind::Number(magnitude) = &value.kind =>
        {
            let ty = numeral_type(module, expression.span, expected, true, prelude)?;
            checked.sites.push(LiteralSite {
                module,
                span: expression.span,
                ty: type_symbol(ty, prelude),
                value: elaborate_numeral(
                    module,
                    expression.span,
                    magnitude.clone(),
                    true,
                    ty,
                    prelude,
                )?,
            });
            Some(named(type_symbol(ty, prelude)))
        }
        h::ExprKind::Unary(_, value) => infer_expr(
            module,
            value,
            expected,
            environment,
            prelude,
            locals,
            checked,
        )?,
        h::ExprKind::Binary(operator, left, right) => {
            let operand_expected = match operator {
                super::ast::BinaryOp::Add
                | super::ast::BinaryOp::Subtract
                | super::ast::BinaryOp::Multiply
                | super::ast::BinaryOp::Divide
                | super::ast::BinaryOp::Remainder => expected,
                _ => None,
            };
            let left_type = infer_expr(
                module,
                left,
                operand_expected,
                environment,
                prelude,
                locals,
                checked,
            )?;
            infer_expr(
                module,
                right,
                operand_expected.or(left_type.as_ref()),
                environment,
                prelude,
                locals,
                checked,
            )?;
            left_type
        }
        h::ExprKind::List(elements, rest) => {
            for element in elements {
                infer_expr(module, element, None, environment, prelude, locals, checked)?;
            }
            if let Some(rest) = rest {
                infer_expr(
                    module,
                    rest,
                    expected,
                    environment,
                    prelude,
                    locals,
                    checked,
                )?;
            }
            expected.cloned()
        }
        h::ExprKind::Lambda(_, body) => {
            infer_expr(module, body, None, environment, prelude, locals, checked)?;
            expected.cloned()
        }
        h::ExprKind::Member(receiver, _) => {
            infer_expr(
                module,
                receiver,
                None,
                environment,
                prelude,
                locals,
                checked,
            )?;
            expected.cloned()
        }
        h::ExprKind::Method(receiver, _, arguments) => {
            infer_expr(
                module,
                receiver,
                None,
                environment,
                prelude,
                locals,
                checked,
            )?;
            for argument in arguments {
                infer_expr(
                    module,
                    argument,
                    None,
                    environment,
                    prelude,
                    locals,
                    checked,
                )?;
            }
            expected.cloned()
        }
    };
    if let (Some(expected), Some(inferred)) = (expected, inferred.as_ref())
        && !matches!(inferred, h::Type::Function(..))
    {
        ensure_same(module, expression.span, inferred, expected)?;
    }
    Ok(inferred.or_else(|| expected.cloned()))
}

fn elaborate_numeral(
    module: ModuleId,
    span: super::ast::Span,
    magnitude: num_bigint::BigUint,
    negative: bool,
    ty: NumeralType,
    prelude: &PreludeIds,
) -> Result<LiteralExpr, CheckError> {
    blessed::numeral(magnitude, negative, ty, prelude)
        .map_err(|error| failure(module, span, error.to_string()))
}

fn numeral_type(
    module: ModuleId,
    span: super::ast::Span,
    expected: Option<&h::Type>,
    negative: bool,
    prelude: &PreludeIds,
) -> Result<NumeralType, CheckError> {
    match expected {
        Some(h::Type::Named(name, _)) if *name == prelude.nat && !negative => Ok(NumeralType::Nat),
        Some(h::Type::Named(name, _)) if *name == prelude.nat => {
            Err(failure(module, span, "a negative numeral cannot be a Nat"))
        }
        Some(h::Type::Named(name, _)) if *name == prelude.int => Ok(NumeralType::Int),
        Some(_) => Err(failure(
            module,
            span,
            "a numeral in this frontend slice must be a Nat or Int",
        )),
        None if negative => Ok(NumeralType::Int),
        None => Ok(NumeralType::Nat),
    }
}

const fn type_symbol(ty: NumeralType, prelude: &PreludeIds) -> Symbol {
    match ty {
        NumeralType::Nat => prelude.nat,
        NumeralType::Int => prelude.int,
    }
}

const fn named(symbol: Symbol) -> h::Type {
    h::Type::Named(symbol, Vec::new())
}

fn ensure_same(
    module: ModuleId,
    span: super::ast::Span,
    actual: &h::Type,
    expected: &h::Type,
) -> Result<(), CheckError> {
    if actual == expected
        || matches!(actual, h::Type::Variable(_))
        || matches!(expected, h::Type::Variable(_))
    {
        Ok(())
    } else {
        Err(failure(
            module,
            span,
            "expression does not match its expected type",
        ))
    }
}

fn failure(module: ModuleId, span: super::ast::Span, message: impl Into<String>) -> CheckError {
    CheckError {
        module,
        span,
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{blessed::PreludeIds, modules, resolve};
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
            let root = std::env::temp_dir().join(format!("faun-check-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).unwrap();
            path
        }

        fn load(&self, entry_source: &str) -> (PreludeIds, resolve::ResolvedProgram) {
            self.write("nat.ori", "exports {Nat.*}\nNat : [Zero Succ(Nat)]\n");
            self.write(
                "int.ori",
                "exports {Int.*}\nInt : [Pos(Nat) NegSucc(Nat)].(of_nat : Nat -> Int of_nat(n) -> Pos(n) neg : Int -> Int neg(i) -> i)\n",
            );
            self.write("u8.ori", "exports {U8}\nU8 : Nat\n");
            self.write(
                "list.ori",
                "exports {List.*}\nList(a) : [Nil Cons(a List(a))]\n",
            );
            self.write("str.ori", "exports {Str}\nStr : List(U8)\n");
            let standard = self.write(
                "standard.ori",
                "lib {}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8}\nimport list {List.*}\nimport str {Str}\nexports {Nat.* Int.* U8 List.* Str}\n",
            );
            let entry = self.write("main.ori", entry_source);
            let loaded = modules::load(&[entry], Some(&standard)).unwrap();
            let prelude = PreludeIds::resolve(&loaded).unwrap();
            let resolved = resolve::resolve(loaded).unwrap();
            (prelude, resolved)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn context_selects_nat_int_and_str_elaboration() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load(
            "natural : Nat\nnatural() -> 42\ninteger : Int\ninteger() -> -42\ntext : Str\ntext() -> \"é\"\n",
        );
        let checked = literals(&resolved.program, &prelude).unwrap();
        let entry = resolved.program.modules.last().unwrap().source;
        let entry_sites: Vec<_> = checked
            .sites
            .iter()
            .filter(|site| site.module == entry)
            .collect();
        assert_eq!(entry_sites.len(), 3);
        assert_eq!(entry_sites[0].ty, prelude.nat);
        assert_eq!(entry_sites[1].ty, prelude.int);
        assert_eq!(entry_sites[2].ty, prelude.str_);
        assert!(matches!(
            entry_sites[1].value,
            LiteralExpr::Call(function, _) if function == prelude.int_neg
        ));
    }

    #[test]
    fn repository_bootstrap_prelude_checks_literal_example() {
        let root =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../standard/ori/standard.ori");
        let entry =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../notes/examples/literals.ori");
        let loaded = modules::load(&[entry], Some(&root)).unwrap();
        let prelude = PreludeIds::resolve(&loaded).unwrap();
        let resolved = resolve::resolve(loaded).unwrap();
        let checked = literals(&resolved.program, &prelude).unwrap();
        let entry = resolved.program.modules.last().unwrap().source;
        assert_eq!(
            checked
                .sites
                .iter()
                .filter(|site| site.module == entry)
                .count(),
            3
        );
    }

    #[test]
    fn a_negative_nat_is_rejected() {
        let fixture = Fixture::new();
        let (prelude, resolved) = fixture.load("bad : Nat\nbad() -> -1\n");
        let failure = literals(&resolved.program, &prelude).unwrap_err();
        assert!(failure.message.contains("negative numeral"));
    }
}
