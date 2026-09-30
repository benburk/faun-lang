//! Compile ordered clauses and irrefutable bindings into explicit decisions.
//!
//! This pass owns pattern normalization, guard fallthrough, numeral testing and
//! destructuring. It consumes first-order HIR and produces a program with no
//! source patterns; Barb emission only assigns backend IDs and emits decisions.

#![allow(clippy::too_many_lines)]

use std::collections::HashMap;

use num_traits::ToPrimitive;

use crate::blessed::PreludeIds;
use crate::declarations::Data;
use crate::diagnostic::LowerError;
use crate::first_order::{self as d, Expr, ExprKind};
use crate::hir::LocalId;
use crate::specialize::{FunctionKey, Pattern, Type};
use crate::{Symbol, Symbols};

#[derive(Clone, Debug)]
pub(crate) struct Program {
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, Data>,
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) key: FunctionKey,
    pub(crate) definition: Definition,
}

#[derive(Clone, Debug)]
pub(crate) enum Definition {
    External(Symbol),
    Body(Box<Decision>),
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) bindings: Vec<Binding>,
    pub(crate) result: Expr,
}

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub(crate) unpack: Unpack,
    pub(crate) value: Expr,
}

/// Every unpack has one possible constructor and fields in declaration order.
#[derive(Clone, Debug)]
pub(crate) enum Unpack {
    Ignore,
    Bind(LocalId),
    Fields { owner: Type, fields: Vec<Self> },
}

/// Compile every function, including ones an entry does not reach.
pub(crate) fn compile(
    program: d::Program,
    prelude: &PreludeIds,
    symbols: &Symbols,
) -> Result<Program, LowerError> {
    let compiler = Compiler {
        data: &program.data,
        prelude,
        symbols,
    };
    let functions = program
        .functions
        .into_iter()
        .map(|function| {
            let definition = match function.definition {
                d::Definition::External(provider) => Definition::External(provider),
                d::Definition::Body(clauses) => {
                    let subjects: Vec<_> = function
                        .key
                        .signature
                        .parameters
                        .iter()
                        .enumerate()
                        .map(|(index, ty)| Subject {
                            value: Value(u32::try_from(index).expect("a sane arity")),
                            ty: ty.clone(),
                        })
                        .collect();
                    let rows = clauses
                        .into_iter()
                        .map(|clause| {
                            Ok(Row {
                                patterns: clause.patterns,
                                guard: clause.guard,
                                body: compiler.body(clause.body)?,
                                locals: HashMap::new(),
                            })
                        })
                        .collect::<Result<Vec<_>, LowerError>>()?;
                    let mut next = u32::try_from(subjects.len()).expect("a sane arity");
                    Definition::Body(Box::new(compiler.plan(&rows, &subjects, &mut next)?))
                }
            };
            Ok(Function {
                key: function.key,
                definition,
            })
        })
        .collect::<Result<_, LowerError>>()?;
    Ok(Program {
        entry: program.entry,
        functions,
        data: program.data,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Value(pub(crate) u32);

#[derive(Clone, Debug)]
struct Subject {
    value: Value,
    ty: Type,
}

#[derive(Clone, Debug)]
struct Row {
    patterns: Vec<Pattern>,
    guard: Option<Expr>,
    body: Body,
    locals: HashMap<LocalId, Value>,
}

#[derive(Clone, Debug)]
pub(crate) enum Decision {
    Body {
        body: Body,
        locals: HashMap<LocalId, Value>,
    },
    Match {
        subject: Value,
        owner: Type,
        arms: Vec<DecisionArm>,
    },
    Record {
        subject: Value,
        owner: Type,
        fields: Vec<Value>,
        decision: Box<Self>,
    },
    /// The condition is a body: a guard written as a block has its
    /// bindings, taken out ahead of its test.
    Guard {
        condition: Body,
        locals: HashMap<LocalId, Value>,
        false_constructor: Symbol,
        true_constructor: Symbol,
        otherwise: Box<Self>,
        answer: Box<Self>,
    },
    /// Whether a natural is a numeral: one test, where taking the numeral's
    /// successors off one at a time would be as many matches as it counts.
    Numeral {
        subject: Value,
        number: num_bigint::BigUint,
        equal: Box<Self>,
        otherwise: Box<Self>,
    },
}

impl Decision {
    pub(crate) fn tests_numerals(&self) -> bool {
        match self {
            Self::Body { .. } => false,
            Self::Numeral { .. } => true,
            Self::Match { arms, .. } => arms.iter().any(|arm| arm.decision.tests_numerals()),
            Self::Record { decision, .. } => decision.tests_numerals(),
            Self::Guard {
                otherwise, answer, ..
            } => otherwise.tests_numerals() || answer.tests_numerals(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct DecisionArm {
    pub(crate) constructor: Symbol,
    pub(crate) fields: Vec<Value>,
    pub(crate) decision: Box<Decision>,
}

/// The largest numeral a column of naturals is taken apart for rather than
/// tested against. See [`Compiler::numeral_column`].
const PEELED_NUMERALS: u8 = 8;

struct Compiler<'a> {
    data: &'a HashMap<Symbol, Data>,
    prelude: &'a PreludeIds,
    symbols: &'a Symbols,
}

impl Compiler<'_> {
    fn body(&self, body: d::Body) -> Result<Body, LowerError> {
        let body = hoisted(body);
        let bindings = body
            .bindings
            .into_iter()
            .map(|binding| {
                let unpack =
                    self.unpack(binding.pattern, &binding.value.ty)
                        .map_err(|mut error| {
                            error.at = Some((binding.value.module, binding.value.span));
                            error
                        })?;
                Ok(Binding {
                    unpack,
                    value: binding.value,
                })
            })
            .collect::<Result<_, LowerError>>()?;
        Ok(Body {
            bindings,
            result: body.result,
        })
    }

    fn unpack(&self, pattern: Pattern, ty: &Type) -> Result<Unpack, LowerError> {
        let fields = match (pattern, ty) {
            (Pattern::Wild, _) => return Ok(Unpack::Ignore),
            (Pattern::Bind(local), _) => return Ok(Unpack::Bind(local)),
            (Pattern::Record(named), Type::Record(fields)) => {
                let mut named: HashMap<_, _> = named.into_iter().collect();
                let fields = fields
                    .iter()
                    .map(|(name, ty)| self.unpack(named.remove(name).unwrap_or(Pattern::Wild), ty))
                    .collect::<Result<_, _>>()?;
                if !named.is_empty() {
                    return Err(error("a record pattern names a field its type lacks"));
                }
                fields
            }
            (Pattern::Product(members), Type::Tuple(types)) => members
                .into_iter()
                .zip(types)
                .map(|(pattern, ty)| self.unpack(pattern, ty))
                .collect::<Result<_, _>>()?,
            (Pattern::Constructor(constructor, patterns), Type::Named(..)) => {
                let constructors = ty.constructors(self.data)?;
                let [(only, fields)] = constructors.as_slice() else {
                    return Err(error(format!(
                        "a binding takes apart only what always matches, and `{}` is one of several constructors",
                        source_name(constructor, self.symbols)
                    )));
                };
                debug_assert_eq!(*only, constructor, "checking matched the constructor");
                patterns
                    .into_iter()
                    .zip(fields)
                    .map(|(pattern, ty)| self.unpack(pattern, ty))
                    .collect::<Result<_, _>>()?
            }
            _ => {
                return Err(error(
                    "a binding takes a value apart only as names, records, tuples and a type's one constructor, which always match",
                ));
            }
        };
        Ok(Unpack::Fields {
            owner: ty.clone(),
            fields,
        })
    }

    fn plan(
        &self,
        rows: &[Row],
        subjects: &[Subject],
        next: &mut u32,
    ) -> Result<Decision, LowerError> {
        if rows.is_empty() {
            return Err(error("function clauses are not exhaustive"));
        }
        let mut first = rows[0].clone();
        if first.patterns.iter().all(irrefutable) {
            for (pattern, subject) in first.patterns.iter().zip(subjects) {
                if let Pattern::Bind(local) = pattern {
                    first.locals.insert(*local, subject.value);
                }
            }
            let answer = Decision::Body {
                body: first.body,
                locals: first.locals.clone(),
            };
            let Some(condition) = first.guard else {
                return Ok(answer);
            };
            let booleans = Type::Named(self.prelude.bool_, Vec::new()).constructors(self.data)?;
            if booleans.len() != 2
                || booleans.iter().any(|(_, fields)| !fields.is_empty())
                || !booleans
                    .iter()
                    .any(|(name, _)| *name == self.prelude.bool_false)
                || !booleans
                    .iter()
                    .any(|(name, _)| *name == self.prelude.bool_true)
            {
                return Err(error(
                    "Bool must have fieldless False and True constructors",
                ));
            }
            let condition = self.body(d::Body {
                bindings: Vec::new(),
                result: condition,
            })?;
            return Ok(Decision::Guard {
                condition,
                locals: first.locals,
                false_constructor: self.prelude.bool_false,
                true_constructor: self.prelude.bool_true,
                otherwise: Box::new(self.plan(&rows[1..], subjects, next)?),
                answer: Box::new(answer),
            });
        }
        let column = rows
            .iter()
            .flat_map(|row| row.patterns.iter().enumerate())
            .find(|(_, pattern)| !irrefutable(pattern))
            .map(|(column, _)| column)
            .expect("a refutable pattern exists");
        let subject = &subjects[column];
        if let Some(member_types) = subject.ty.members() {
            let fields: Vec<_> = member_types
                .iter()
                .map(|_| {
                    let value = Value(*next);
                    *next = next.checked_add(1).expect("fewer than 2^32 plan values");
                    value
                })
                .collect();
            let mut specialized = Vec::with_capacity(rows.len());
            for mut row in rows.iter().cloned() {
                let normalized =
                    self.normalize_pattern(row.patterns[column].clone(), &subject.ty)?;
                let replacement = match normalized {
                    Pattern::Wild => vec![Pattern::Wild; fields.len()],
                    Pattern::Bind(local) => {
                        row.locals.insert(local, subject.value);
                        vec![Pattern::Wild; fields.len()]
                    }
                    Pattern::Product(patterns) => patterns,
                    _ => unreachable!("record and tuple patterns normalize to a product"),
                };
                if replacement.len() != fields.len() {
                    return Err(error("a product pattern has the wrong field count"));
                }
                row.patterns.splice(column..=column, replacement);
                specialized.push(row);
            }
            let mut nested_subjects = subjects.to_vec();
            nested_subjects.splice(
                column..=column,
                fields
                    .iter()
                    .copied()
                    .zip(member_types)
                    .map(|(value, ty)| Subject { value, ty }),
            );
            return Ok(Decision::Record {
                subject: subject.value,
                owner: subject.ty.clone(),
                fields,
                decision: Box::new(self.plan(&specialized, &nested_subjects, next)?),
            });
        }
        if let Some(number) = self.numeral_column(rows, column, &subject.ty) {
            let mut equal = Vec::new();
            let mut otherwise = Vec::new();
            for row in rows {
                match &row.patterns[column] {
                    Pattern::Number { magnitude, .. } if *magnitude == number => {
                        let mut row = row.clone();
                        row.patterns[column] = Pattern::Wild;
                        equal.push(row);
                    }
                    Pattern::Number { .. } => otherwise.push(row.clone()),
                    _ => {
                        equal.push(row.clone());
                        otherwise.push(row.clone());
                    }
                }
            }
            return Ok(Decision::Numeral {
                subject: subject.value,
                number,
                equal: Box::new(self.plan(&equal, subjects, next)?),
                otherwise: Box::new(self.plan(&otherwise, subjects, next)?),
            });
        }
        let constructors = subject.ty.constructors(self.data)?;
        let mut arms = Vec::with_capacity(constructors.len());
        for (constructor, field_types) in constructors {
            let fields: Vec<_> = field_types
                .iter()
                .map(|_| {
                    let value = Value(*next);
                    *next = next.checked_add(1).expect("fewer than 2^32 plan values");
                    value
                })
                .collect();
            let mut specialized = Vec::new();
            for mut row in rows.iter().cloned() {
                let normalized =
                    self.normalize_pattern(row.patterns[column].clone(), &subject.ty)?;
                let replacement = match normalized {
                    Pattern::Wild => vec![Pattern::Wild; fields.len()],
                    Pattern::Bind(local) => {
                        row.locals.insert(local, subject.value);
                        vec![Pattern::Wild; fields.len()]
                    }
                    Pattern::Constructor(found, patterns) if found == constructor => patterns,
                    Pattern::Constructor(_, _) => continue,
                    _ => unreachable!("patterns normalize to wildcard, bind, or constructor"),
                };
                if replacement.len() != fields.len() {
                    return Err(error("constructor pattern has the wrong field count"));
                }
                row.patterns.splice(column..=column, replacement);
                specialized.push(row);
            }
            let mut arm_subjects = subjects.to_vec();
            arm_subjects.splice(
                column..=column,
                fields
                    .iter()
                    .copied()
                    .zip(field_types)
                    .map(|(value, ty)| Subject { value, ty }),
            );
            arms.push(DecisionArm {
                constructor,
                fields,
                decision: Box::new(self.plan(&specialized, &arm_subjects, next)?),
            });
        }
        Ok(Decision::Match {
            subject: subject.value,
            owner: subject.ty.clone(),
            arms,
        })
    }

    /// The numeral a column of naturals is first tested for, where every
    /// pattern in it is a numeral or takes anything, and some numeral is
    /// past [`PEELED_NUMERALS`]: then each is one test.
    ///
    /// A small numeral is taken apart instead, a successor at a time. That
    /// is as few matches as tests, and what it says is more: past `0` a
    /// number is a successor, which a definition counting down takes apart.
    /// A column also taking successors apart is taken apart,
    /// numerals and all, since a test says nothing about what a successor
    /// holds.
    fn numeral_column(
        &self,
        rows: &[Row],
        column: usize,
        ty: &Type,
    ) -> Option<num_bigint::BigUint> {
        if *ty != Type::Named(self.prelude.nat, Vec::new()) {
            return None;
        }
        let mut first = None;
        let mut largest = num_bigint::BigUint::ZERO;
        for row in rows {
            match &row.patterns[column] {
                Pattern::Number {
                    magnitude,
                    negative: false,
                } => {
                    first.get_or_insert_with(|| magnitude.clone());
                    largest = largest.max(magnitude.clone());
                }
                Pattern::Wild | Pattern::Bind(_) => {}
                _ => return None,
            }
        }
        first.filter(|_| largest > num_bigint::BigUint::from(PEELED_NUMERALS))
    }

    fn normalize_pattern(&self, pattern: Pattern, expected: &Type) -> Result<Pattern, LowerError> {
        match pattern {
            Pattern::Number {
                magnitude,
                negative,
            } => self.number_pattern(magnitude, negative, expected),
            Pattern::Range => Err(error(
                "a range pattern is a test, which only a clause's guard makes",
            )),
            Pattern::String => Err(error(
                "a string pattern is a test, which only a clause's guard makes",
            )),
            Pattern::List(elements, rest) => {
                let mut tail = rest.map_or(
                    Pattern::Constructor(self.prelude.list_nil, Vec::new()),
                    |rest| *rest,
                );
                for element in elements.into_iter().rev() {
                    tail = Pattern::Constructor(self.prelude.list_cons, vec![element, tail]);
                }
                Ok(tail)
            }
            // A field the pattern does not name is taken whatever it is.
            Pattern::Record(mut fields) => {
                let Type::Record(expected) = expected else {
                    return Err(error("record pattern does not have a record type"));
                };
                if fields
                    .iter()
                    .any(|(found, _)| !expected.iter().any(|(wanted, _)| wanted == found))
                {
                    return Err(error("record pattern names a field its type lacks"));
                }
                Ok(Pattern::Product(
                    expected
                        .iter()
                        .map(|(wanted, _)| {
                            fields
                                .iter()
                                .position(|(found, _)| found == wanted)
                                .map_or(Pattern::Wild, |at| fields.swap_remove(at).1)
                        })
                        .collect(),
                ))
            }
            product @ Pattern::Product(_) => Ok(product),
            other => Ok(other),
        }
    }

    fn number_pattern(
        &self,
        magnitude: num_bigint::BigUint,
        negative: bool,
        expected: &Type,
    ) -> Result<Pattern, LowerError> {
        let Type::Named(name, arguments) = expected else {
            return Err(error("numeric pattern does not have a named type"));
        };
        if !arguments.is_empty() {
            return Err(error("numeric pattern type unexpectedly has arguments"));
        }
        if *name == self.prelude.nat {
            if negative {
                return Err(error("a negative pattern cannot match Nat"));
            }
            return self.natural_pattern(&magnitude);
        }
        if *name == self.prelude.int {
            let constructors = &self.data[name].constructors;
            if constructors.len() != 2 {
                return Err(error("Int must have positive and negative constructors"));
            }
            // The natural inside is a numeral too, tested where it is taken
            // apart rather than counted down here.
            if negative && magnitude != num_bigint::BigUint::ZERO {
                let predecessor = magnitude - 1u8;
                return Ok(Pattern::Constructor(
                    constructors[1].name,
                    vec![Pattern::Number {
                        magnitude: predecessor,
                        negative: false,
                    }],
                ));
            }
            return Ok(Pattern::Constructor(
                constructors[0].name,
                vec![Pattern::Number {
                    magnitude,
                    negative: false,
                }],
            ));
        }
        Err(error("a numeric pattern must infer as Nat or Int"))
    }

    fn natural_pattern(&self, magnitude: &num_bigint::BigUint) -> Result<Pattern, LowerError> {
        const MAX_PATTERN_MAGNITUDE: usize = 1_024;
        let count = magnitude
            .to_usize()
            .filter(|count| *count <= MAX_PATTERN_MAGNITUDE)
            .ok_or_else(|| error("numeric pattern is too large to lower structurally"))?;
        let constructors = &self.data[&self.prelude.nat].constructors;
        if constructors.len() != 2
            || !constructors[0].fields.is_empty()
            || constructors[1].fields.len() != 1
        {
            return Err(error("Nat does not have the required zero/successor shape"));
        }
        let mut pattern = Pattern::Constructor(constructors[0].name, Vec::new());
        for _ in 0..count {
            pattern = Pattern::Constructor(constructors[1].name, vec![pattern]);
        }
        Ok(pattern)
    }
}

/// `body` with every `value?` in it bound on its own, in the order it is
/// evaluated, and read back where it was written: what follows a `?` runs
/// only on its `Ok`. A block's bindings are taken out the same way, ahead of
/// the expression it stands in, and its answer read where it was written;
/// its locals are numbered apart from the clause's others, so none is
/// captured. Evaluation is pure but for effects, which stand on their own,
/// so taking either out ahead of the rest of its expression changes nothing
/// a program can see.
fn hoisted(body: d::Body) -> d::Body {
    let mut fresh = 0;
    let mut bindings = Vec::with_capacity(body.bindings.len());
    for binding in body.bindings {
        let value = lifted(binding.value, &mut bindings, &mut fresh);
        bindings.push(d::Binding {
            pattern: binding.pattern,
            value,
        });
    }
    let result = lifted(body.result, &mut bindings, &mut fresh);
    d::Body { bindings, result }
}

/// `expression` with each `?` in it replaced by a local bound before it, and
/// each block by its answer, its bindings bound before it.
fn lifted(expression: Expr, bindings: &mut Vec<d::Binding>, fresh: &mut u32) -> Expr {
    if let ExprKind::Block(block) = expression.kind {
        for binding in block.bindings {
            let value = lifted(binding.value, bindings, fresh);
            bindings.push(d::Binding {
                pattern: binding.pattern,
                value,
            });
        }
        return lifted(block.result, bindings, fresh);
    }
    let mut lift = |inner: Expr| lifted(inner, bindings, fresh);
    let kind = match expression.kind {
        ExprKind::Block(_) => unreachable!("taken out above"),
        ExprKind::Local(_) | ExprKind::Natural(_) | ExprKind::Bytes(_) => {
            return expression;
        }
        ExprKind::Construct(constructor, fields) => {
            ExprKind::Construct(constructor, fields.into_iter().map(&mut lift).collect())
        }
        ExprKind::Record(fields) => ExprKind::Record(
            fields
                .into_iter()
                .map(|(name, field)| (name, lift(field)))
                .collect(),
        ),
        ExprKind::Tuple(members) => ExprKind::Tuple(members.into_iter().map(&mut lift).collect()),
        ExprKind::Update(base, fields) => {
            let base = lift(*base);
            ExprKind::Update(
                Box::new(base),
                fields
                    .into_iter()
                    .map(|(name, field)| (name, lift(field)))
                    .collect(),
            )
        }
        ExprKind::Project(receiver, field) => ExprKind::Project(Box::new(lift(*receiver)), field),
        ExprKind::DirectCall(key, arguments) => {
            ExprKind::DirectCall(key, arguments.into_iter().map(&mut lift).collect())
        }
        ExprKind::Widen(value) => ExprKind::Widen(Box::new(lift(*value))),
        ExprKind::Try(value) => {
            let value = lift(*value);
            // Past any local a clause can have: they are numbered from nought.
            let local = LocalId(u32::MAX - *fresh);
            *fresh += 1;
            bindings.push(d::Binding {
                pattern: Pattern::Bind(local),
                value: Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::Try(Box::new(value)),
                },
            });
            ExprKind::Local(local)
        }
    };
    Expr {
        module: expression.module,
        span: expression.span,
        ty: expression.ty,
        kind,
    }
}

const fn irrefutable(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Wild | Pattern::Bind(_))
}

fn source_name(symbol: Symbol, symbols: &Symbols) -> &str {
    // Resolution prefixes globals with a module identity separated by `$$`.
    let canonical = symbols.text(symbol);
    canonical
        .rsplit_once("$$")
        .map_or(canonical, |(_, spelling)| spelling)
}

fn error(message: impl Into<String>) -> LowerError {
    LowerError::new(message.into(), None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked() -> crate::check::CheckedProgram {
        let root = crate::standard_path();
        let entry =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/lowering.fn");
        let loaded = crate::modules::load_program(&entry, root, &crate::test_host()).unwrap();
        let prelude = PreludeIds::find_in(&loaded).unwrap();
        let resolved = crate::resolve::resolve_names(loaded).unwrap();
        crate::check::type_check(crate::declarations::normalize(resolved), prelude).unwrap()
    }

    fn row(pattern: Pattern, checked: &crate::check::CheckedProgram) -> Row {
        let prelude = &checked.prelude;
        Row {
            patterns: vec![pattern],
            guard: None,
            locals: HashMap::new(),
            body: Body {
                bindings: Vec::new(),
                result: Expr {
                    module: checked.resolved.program.functions[0].module,
                    span: crate::ast::Span::default(),
                    ty: Type::Named(prelude.nat, Vec::new()),
                    kind: ExprKind::Natural(0u32.into()),
                },
            },
        }
    }

    #[test]
    fn numeral_threshold_and_guard_fallthrough_survive_planning() {
        let checked = checked();
        let prelude = &checked.prelude;
        let compiler = Compiler {
            data: &checked.resolved.program.data,
            prelude,
            symbols: &checked.resolved.symbols,
        };
        let subjects = [Subject {
            value: Value(0),
            ty: Type::Named(prelude.nat, Vec::new()),
        }];
        for (number, tested) in [(8u32, false), (9, true)] {
            let rows = [
                row(
                    Pattern::Number {
                        magnitude: number.into(),
                        negative: false,
                    },
                    &checked,
                ),
                row(Pattern::Wild, &checked),
            ];
            let plan = compiler.plan(&rows, &subjects, &mut 1).unwrap();
            assert_eq!(plan.tests_numerals(), tested);
            assert_eq!(matches!(plan, Decision::Match { .. }), !tested);
        }
        let mut guarded = row(Pattern::Wild, &checked);
        guarded.guard = Some(Expr {
            ty: Type::Named(prelude.bool_, Vec::new()),
            kind: ExprKind::Construct(prelude.bool_false, Vec::new()),
            ..guarded.body.result.clone()
        });
        let plan = compiler
            .plan(&[guarded, row(Pattern::Wild, &checked)], &subjects, &mut 1)
            .unwrap();
        let Decision::Guard {
            answer, otherwise, ..
        } = plan
        else {
            panic!("a guard must retain both continuations")
        };
        assert!(matches!(*answer, Decision::Body { .. }));
        assert!(matches!(*otherwise, Decision::Body { .. }));
    }

    #[test]
    fn unpacks_are_ordered_and_refutable_bindings_keep_their_source() {
        let mut checked = checked();
        let a = checked.resolved.symbols.intern("a");
        let b = checked.resolved.symbols.intern("b");
        let prelude = &checked.prelude;
        let compiler = Compiler {
            data: &checked.resolved.program.data,
            prelude,
            symbols: &checked.resolved.symbols,
        };
        let nat = Type::Named(prelude.nat, Vec::new());
        let record = Type::Record(vec![(a, nat.clone()), (b, nat)]);
        let unpack = compiler
            .unpack(
                Pattern::Record(vec![(b, Pattern::Bind(LocalId(3)))]),
                &record,
            )
            .unwrap();
        let Unpack::Fields { fields, .. } = unpack else {
            panic!("a record becomes an unpack")
        };
        assert!(matches!(
            fields.as_slice(),
            [Unpack::Ignore, Unpack::Bind(LocalId(3))]
        ));
        let value = row(Pattern::Wild, &checked).body.result;
        let constructor = compiler.data[&prelude.nat].constructors[0].name;
        let failure = compiler
            .body(d::Body {
                bindings: vec![d::Binding {
                    pattern: Pattern::Constructor(constructor, Vec::new()),
                    value: value.clone(),
                }],
                result: value.clone(),
            })
            .unwrap_err();
        assert_eq!(failure.at, Some((value.module, value.span)));
        assert!(failure.message.contains("one of several constructors"));
    }
}
