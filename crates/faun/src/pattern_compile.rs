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
use crate::specialize::{FunctionKey, Pattern, Split, Type};
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
    pub(crate) value: Bound,
}

/// What a binding binds.
#[derive(Clone, Debug)]
pub(crate) enum Bound {
    Value(Expr),
    /// `if condition then yes else no`, the condition a `Bool` worked out
    /// ahead of it and each branch a body of its own, worked out only where
    /// it is chosen.
    If {
        condition: Expr,
        yes: Box<Body>,
        no: Box<Body>,
    },
    /// `if subject is pattern then yes else no`: a decision on the subject,
    /// which is its value nought, each branch a body in it, what the
    /// pattern binds in scope in `yes`.
    Match {
        subject: Expr,
        decision: Box<Decision>,
    },
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
        run_out: RunOut::Refused,
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
                                guard: clause
                                    .guard
                                    .map(|guard| asked(guard, prelude))
                                    .unwrap_or_default(),
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
    /// What the row's guard asks, in turn; see [`asked`].
    guard: Vec<Expr>,
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
    /// `value` worked out by `subject` where the row's patterns have
    /// matched, as a guard's test asks of it, and what is decided of it.
    Let {
        value: Value,
        subject: Body,
        locals: HashMap<LocalId, Value>,
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
    /// A list split before its last `count` elements, or before all of them
    /// where it holds fewer: `front` is `take(subject, c)` and `back` is
    /// `drop(subject, c)`, where `c` is `len(drop(subject, count))`.
    Split {
        subject: Value,
        count: usize,
        len: FunctionKey,
        take: FunctionKey,
        drop: FunctionKey,
        front: Value,
        back: Value,
        decision: Box<Self>,
    },
    /// A way no value takes, below a split of `subject`, of type `ty`; see
    /// [`RunOut::Unreachable`].
    Unreachable { subject: Value, ty: Type },
}

impl Decision {
    pub(crate) fn tests_numerals(&self) -> bool {
        match self {
            Self::Body { .. } | Self::Unreachable { .. } => false,
            Self::Numeral { .. } => true,
            Self::Match { arms, .. } => arms.iter().any(|arm| arm.decision.tests_numerals()),
            Self::Record { decision, .. }
            | Self::Split { decision, .. }
            | Self::Let { decision, .. } => decision.tests_numerals(),
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

#[derive(Clone)]
struct Compiler<'a> {
    data: &'a HashMap<Symbol, Data>,
    prelude: &'a PreludeIds,
    symbols: &'a Symbols,
    run_out: RunOut,
}

/// What a plan makes of a way no row is left for.
#[derive(Clone)]
enum RunOut {
    /// Some value matches no clause, which is refused.
    Refused,
    /// No value goes this way. Below a split of this list, the list and its
    /// end are both taken apart, and what one decides the other may test
    /// again: a list matched as `Cons` has an end that is not `Nil`. The
    /// clauses were found to cover every value before planning, so a way
    /// they leave is one of those.
    Unreachable(Subject),
}

impl Compiler<'_> {
    fn body(&self, body: d::Body) -> Result<Body, LowerError> {
        let body = d::Body {
            bindings: body
                .bindings
                .into_iter()
                .map(|binding| d::Binding {
                    pattern: binding.pattern,
                    value: tested(binding.value, self.prelude),
                })
                .collect(),
            result: tested(body.result, self.prelude),
        };
        self.compiled(hoisted(body, &mut 0))
    }

    /// `if subject is pattern then yes else no`, as a decision on the
    /// subject: each of the pattern's rows answers `yes`, and any other
    /// value `no`.
    fn test(
        &self,
        subject: Expr,
        alternatives: Vec<(Pattern, Option<Expr>)>,
        yes: d::Body,
        no: d::Body,
    ) -> Result<Bound, LowerError> {
        let subjects = [Subject {
            value: Value(0),
            ty: subject.ty.clone(),
        }];
        let yes = self.compiled(yes)?;
        let mut rows: Vec<Row> = alternatives
            .into_iter()
            .map(|(pattern, guard)| Row {
                patterns: vec![pattern],
                guard: guard.into_iter().collect(),
                body: yes.clone(),
                locals: HashMap::new(),
            })
            .collect();
        rows.push(Row {
            patterns: vec![Pattern::Wild],
            guard: Vec::new(),
            body: self.compiled(no)?,
            locals: HashMap::new(),
        });
        let decision = self.plan(&rows, &subjects, &mut 1)?;
        Ok(Bound::Match {
            subject,
            decision: Box::new(decision),
        })
    }

    /// A body [`hoisted`] already, whose `if`s each stand alone on a line,
    /// their branches hoisted too.
    fn compiled(&self, body: d::Body) -> Result<Body, LowerError> {
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
                let value = match binding.value.kind {
                    ExprKind::If(condition, yes, no) => {
                        let (ExprKind::Block(yes), ExprKind::Block(no)) = (yes.kind, no.kind)
                        else {
                            unreachable!("hoisting makes each branch a block")
                        };
                        match condition.kind {
                            ExprKind::Is(subject, alternatives) => {
                                self.test(*subject, alternatives, *yes, *no)?
                            }
                            _ => Bound::If {
                                condition: *condition,
                                yes: Box::new(self.compiled(*yes)?),
                                no: Box::new(self.compiled(*no)?),
                            },
                        }
                    }
                    _ => Bound::Value(binding.value),
                };
                Ok(Binding { unpack, value })
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
        if rows.iter().any(|row| {
            row.patterns
                .iter()
                .any(|pattern| matches!(pattern, Pattern::As(..)))
        }) {
            let peeled: Vec<Row> = rows.iter().map(|row| named_whole(row, subjects)).collect();
            return self.plan(&peeled, subjects, next);
        }
        let Some(first) = rows.first() else {
            return match &self.run_out {
                RunOut::Refused => Err(error("function clauses are not exhaustive")),
                RunOut::Unreachable(subject) => Ok(Decision::Unreachable {
                    subject: subject.value,
                    ty: subject.ty.clone(),
                }),
            };
        };
        let mut first = first.clone();
        if first.patterns.iter().all(irrefutable) {
            for (pattern, subject) in first.patterns.iter().zip(subjects) {
                if let Pattern::Bind(local) = pattern {
                    first.locals.insert(*local, subject.value);
                }
            }
            if first.guard.is_empty() {
                return Ok(Decision::Body {
                    body: first.body,
                    locals: first.locals,
                });
            }
            let condition = first.guard.remove(0);
            if let ExprKind::Is(subject, alternatives) = condition.kind {
                return self.let_test(first, *subject, alternatives, (rows, subjects), next);
            }
            if let ExprKind::DirectCall(key, _) = &condition.kind
                && key.name == self.prelude.bool_or
                && binds(&condition, self.prelude)
            {
                // Either side, as an `|` among a clause's patterns is: a row
                // for each, the left's tried first.
                let ExprKind::DirectCall(_, sides) = condition.kind else {
                    unreachable!("matched above")
                };
                let mut either = Vec::with_capacity(rows.len() + 1);
                for side in sides {
                    let mut row = first.clone();
                    row.guard = asked(side, self.prelude)
                        .into_iter()
                        .chain(first.guard.iter().cloned())
                        .collect();
                    either.push(row);
                }
                either.extend(rows[1..].iter().cloned());
                return self.plan(&either, subjects, next);
            }
            let otherwise = self.plan(&rows[1..], subjects, next)?;
            let locals = first.locals.clone();
            let mut going_on = vec![first];
            going_on.extend(rows[1..].iter().cloned());
            let answer = self.plan(&going_on, subjects, next)?;
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
                locals,
                false_constructor: self.prelude.bool_false,
                true_constructor: self.prelude.bool_true,
                otherwise: Box::new(otherwise),
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
        if let Some(split) = rows.iter().find_map(|row| ending(&row.patterns[column])) {
            return self.split(rows, subjects, column, split.clone(), next);
        }
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

    /// The rows with `first`'s guard asking `subject is alternatives`
    /// next: the subject worked out as a column of its own, which `first`
    /// matches against each alternative, its rest asked after, and every
    /// other row takes anything in. Where none matches, or what follows
    /// fails, the rows below are tried, as a guard failing is.
    fn let_test(
        &self,
        first: Row,
        subject: Expr,
        alternatives: Vec<(Pattern, Option<Expr>)>,
        (rows, subjects): (&[Row], &[Subject]),
        next: &mut u32,
    ) -> Result<Decision, LowerError> {
        let value = Value(*next);
        *next = next.checked_add(1).expect("fewer than 2^32 plan values");
        let mut tested = subjects.to_vec();
        tested.push(Subject {
            value,
            ty: subject.ty.clone(),
        });
        let mut below = Vec::with_capacity(alternatives.len() + rows.len());
        for (pattern, guard) in alternatives {
            let mut row = first.clone();
            row.patterns.push(pattern);
            row.guard = guard
                .into_iter()
                .chain(first.guard.iter().cloned())
                .collect();
            below.push(row);
        }
        for row in &rows[1..] {
            let mut row = row.clone();
            row.patterns.push(Pattern::Wild);
            below.push(row);
        }
        let subject = self.body(d::Body {
            bindings: Vec::new(),
            result: subject,
        })?;
        Ok(Decision::Let {
            value,
            subject,
            locals: first.locals,
            decision: Box::new(self.plan(&below, &tested, next)?),
        })
    }

    /// Split the list in `column` as `split` does, the front and back two
    /// columns more. Each row ending its list in as many elements matches
    /// them there, taking anything in the list itself; every other row is
    /// left as it was, taking anything in the two.
    fn split(
        &self,
        rows: &[Row],
        subjects: &[Subject],
        column: usize,
        split: Split,
        next: &mut u32,
    ) -> Result<Decision, LowerError> {
        let subject = &subjects[column];
        let count = split.last.len();
        let mut fresh = || {
            let value = Value(*next);
            *next = next.checked_add(1).expect("fewer than 2^32 plan values");
            value
        };
        let (front, back) = (fresh(), fresh());
        let mut specialized = Vec::with_capacity(rows.len());
        for row in rows {
            let mut row = row.clone();
            let (front, back) = match ending(&row.patterns[column]) {
                Some(split) if split.last.len() == count => {
                    let split = split.clone();
                    row.patterns[column] = Pattern::Wild;
                    (split.front, Pattern::List(split.last, None))
                }
                _ => (Pattern::Wild, Pattern::Wild),
            };
            row.patterns.push(front);
            row.patterns.push(back);
            specialized.push(row);
        }
        let mut split_subjects = subjects.to_vec();
        split_subjects.extend([front, back].map(|value| Subject {
            value,
            ty: subject.ty.clone(),
        }));
        let below = Self {
            run_out: RunOut::Unreachable(subject.clone()),
            ..self.clone()
        };
        Ok(Decision::Split {
            subject: subject.value,
            count,
            len: split.len,
            take: split.take,
            drop: split.drop,
            front,
            back,
            decision: Box::new(below.plan(&specialized, &split_subjects, next)?),
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
            Pattern::Ending => Err(error("a list's end is taken apart only by a clause")),
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
///
/// An `if` is bound on its own too, its condition taken out ahead of it and
/// each branch hoisted into a block of its own, since what a branch works
/// out is worked out only where it is chosen. `fresh` counts the locals
/// made so far, across every branch.
fn hoisted(body: d::Body, fresh: &mut u32) -> d::Body {
    let mut bindings = Vec::with_capacity(body.bindings.len());
    for binding in body.bindings {
        let value = lifted(binding.value, &mut bindings, fresh);
        bindings.push(d::Binding {
            pattern: binding.pattern,
            value,
        });
    }
    let result = lifted(body.result, &mut bindings, fresh);
    d::Body { bindings, result }
}

/// `expression` with every test the condition of an `if` of its own: an
/// `if` asking a chain of `&` and `|` holding a test asks each part in
/// turn, as [`branched`] does, so what a test binds is in scope for the
/// rest of the chain and `then`; a test or such a chain standing as a
/// value is an `if` answering `True` or `False`.
fn tested(expression: Expr, prelude: &PreludeIds) -> Expr {
    let Expr {
        module,
        span,
        ty,
        kind,
    } = expression;
    let each = |list: Vec<Expr>| list.into_iter().map(|e| tested(e, prelude)).collect();
    let one = |e: Box<Expr>| Box::new(tested(*e, prelude));
    let kind = match kind {
        ExprKind::If(condition, yes, no) => {
            let yes = tested(*yes, prelude);
            let no = tested(*no, prelude);
            return branched(*condition, yes, no, prelude);
        }
        kind @ ExprKind::Is(..) => {
            let condition = Expr {
                module,
                span,
                ty,
                kind,
            };
            let (yes, no) = (
                boolean(&condition, true, prelude),
                boolean(&condition, false, prelude),
            );
            return branched(condition, yes, no, prelude);
        }
        ExprKind::DirectCall(key, arguments)
            if (key.name == prelude.bool_and || key.name == prelude.bool_or)
                && arguments.iter().any(|a| binds(a, prelude)) =>
        {
            let condition = Expr {
                module,
                span,
                ty,
                kind: ExprKind::DirectCall(key, arguments),
            };
            let (yes, no) = (
                boolean(&condition, true, prelude),
                boolean(&condition, false, prelude),
            );
            return branched(condition, yes, no, prelude);
        }
        kind @ (ExprKind::Local(_) | ExprKind::Natural(_) | ExprKind::Bytes(_)) => kind,
        ExprKind::Construct(constructor, fields) => ExprKind::Construct(constructor, each(fields)),
        ExprKind::Record(fields) => ExprKind::Record(
            fields
                .into_iter()
                .map(|(name, field)| (name, tested(field, prelude)))
                .collect(),
        ),
        ExprKind::Update(base, fields) => ExprKind::Update(
            one(base),
            fields
                .into_iter()
                .map(|(name, field)| (name, tested(field, prelude)))
                .collect(),
        ),
        ExprKind::Tuple(members) => ExprKind::Tuple(each(members)),
        ExprKind::Project(receiver, field) => ExprKind::Project(one(receiver), field),
        ExprKind::DirectCall(key, arguments) => ExprKind::DirectCall(key, each(arguments)),
        ExprKind::Widen(value) => ExprKind::Widen(one(value)),
        ExprKind::Try(value) => ExprKind::Try(one(value)),
        ExprKind::Block(body) => ExprKind::Block(Box::new(d::Body {
            bindings: body
                .bindings
                .into_iter()
                .map(|binding| d::Binding {
                    pattern: binding.pattern,
                    value: tested(binding.value, prelude),
                })
                .collect(),
            result: tested(body.result, prelude),
        })),
    };
    Expr {
        module,
        span,
        ty,
        kind,
    }
}

/// `if condition then yes else no`, `yes` and `no` already [`tested`]:
/// where the condition is a chain of `&` and `|` holding a test, an `if`
/// for each part, so what a test binds is in scope where it held. Past an
/// `&` the right is asked; past an `|`, `yes` answers where the left held
/// and the right is asked where it failed. A branch is copied to each
/// place it is reached from.
fn branched(condition: Expr, yes: Expr, no: Expr, prelude: &PreludeIds) -> Expr {
    let (module, span, ty) = (yes.module, condition.span, yes.ty.clone());
    let header = |kind| Expr {
        module,
        span,
        ty: ty.clone(),
        kind,
    };
    if !binds(&condition, prelude) {
        let condition = tested(condition, prelude);
        return header(ExprKind::If(
            Box::new(condition),
            Box::new(yes),
            Box::new(no),
        ));
    }
    match condition.kind {
        ExprKind::Is(value, pattern) => {
            let part = Expr {
                kind: ExprKind::Is(Box::new(tested(*value, prelude)), pattern),
                ..condition
            };
            header(ExprKind::If(Box::new(part), Box::new(yes), Box::new(no)))
        }
        ExprKind::DirectCall(key, sides) if key.name == prelude.bool_and => {
            sides.into_iter().rev().fold(yes, |answer, side| {
                branched(side, answer, no.clone(), prelude)
            })
        }
        ExprKind::DirectCall(key, sides) if key.name == prelude.bool_or => {
            sides.into_iter().rev().fold(no, |otherwise, side| {
                branched(side, yes.clone(), otherwise, prelude)
            })
        }
        _ => unreachable!("only a test, `&` and `|` bind"),
    }
}

/// What a guard asks, in turn: the parts of a chain of `&` holding a test,
/// each asked where those before it held; anything else, asked whole.
fn asked(guard: Expr, prelude: &PreludeIds) -> Vec<Expr> {
    let mut parts = Vec::new();
    if binds(&guard, prelude) {
        conjuncts(guard, prelude, &mut parts);
    } else {
        parts.push(guard);
    }
    parts
}

/// Whether `expression` is a test, or a chain of `&` and `|` holding one.
fn binds(expression: &Expr, prelude: &PreludeIds) -> bool {
    match &expression.kind {
        ExprKind::Is(..) => true,
        ExprKind::DirectCall(key, arguments)
            if key.name == prelude.bool_and || key.name == prelude.bool_or =>
        {
            arguments.iter().any(|argument| binds(argument, prelude))
        }
        _ => false,
    }
}

/// The parts of a chain of `&`, in order.
fn conjuncts(expression: Expr, prelude: &PreludeIds, parts: &mut Vec<Expr>) {
    match expression.kind {
        ExprKind::DirectCall(key, arguments) if key.name == prelude.bool_and => {
            for argument in arguments {
                conjuncts(argument, prelude, parts);
            }
        }
        kind => parts.push(Expr { kind, ..expression }),
    }
}

/// `True` or `False`, written where `like` is.
const fn boolean(like: &Expr, value: bool, prelude: &PreludeIds) -> Expr {
    let constructor = if value {
        prelude.bool_true
    } else {
        prelude.bool_false
    };
    Expr {
        module: like.module,
        span: like.span,
        ty: Type::Named(prelude.bool_, Vec::new()),
        kind: ExprKind::Construct(constructor, Vec::new()),
    }
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
        ExprKind::Is(..) => unreachable!("each test is an `if`'s condition by now"),
        ExprKind::If(condition, yes, no) => {
            // A test's value is worked out ahead; its pattern is asked by
            // the decision the `if` becomes.
            let condition = match *condition {
                Expr {
                    module,
                    span,
                    ty,
                    kind: ExprKind::Is(value, pattern),
                } => Expr {
                    module,
                    span,
                    ty,
                    kind: ExprKind::Is(Box::new(lift(*value)), pattern),
                },
                condition => lift(condition),
            };
            let branch = |branch: Expr, fresh: &mut u32| {
                let body = d::Body {
                    bindings: Vec::new(),
                    result: branch,
                };
                Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::Block(Box::new(hoisted(body, fresh))),
                }
            };
            let yes = branch(*yes, fresh);
            let no = branch(*no, fresh);
            let local = LocalId(u32::MAX - *fresh);
            *fresh += 1;
            bindings.push(d::Binding {
                pattern: Pattern::Bind(local),
                value: Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::If(Box::new(condition), Box::new(yes), Box::new(no)),
                },
            });
            ExprKind::Local(local)
        }
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

/// The list's end `pattern` takes apart, where it is one: alone, or as the
/// rest of a list naming no element before it.
/// `row` with each whole value its patterns name bound to its subject,
/// and taken apart by what the name stood for.
fn named_whole(row: &Row, subjects: &[Subject]) -> Row {
    let mut row = row.clone();
    for (pattern, subject) in row.patterns.iter_mut().zip(subjects) {
        while let Pattern::As(local, inner) = pattern {
            row.locals.insert(*local, subject.value);
            *pattern = std::mem::replace(&mut **inner, Pattern::Wild);
        }
    }
    row
}

fn ending(pattern: &Pattern) -> Option<&Split> {
    match pattern {
        Pattern::Split(split) => Some(split),
        Pattern::List(elements, Some(rest)) if elements.is_empty() => ending(rest),
        _ => None,
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
            guard: Vec::new(),
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
            run_out: RunOut::Refused,
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
        guarded.guard = vec![Expr {
            ty: Type::Named(prelude.bool_, Vec::new()),
            kind: ExprKind::Construct(prelude.bool_false, Vec::new()),
            ..guarded.body.result.clone()
        }];
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
            run_out: RunOut::Refused,
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
