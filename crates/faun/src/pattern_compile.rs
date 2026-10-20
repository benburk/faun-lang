//! Compile ordered clauses and irrefutable bindings into explicit decisions.
//!
//! This pass owns pattern normalization, guard fallthrough, numeral testing and
//! destructuring. It consumes first-order HIR and produces a program with no
//! source patterns; Barb emission only assigns backend IDs and emits decisions.

#![allow(clippy::too_many_lines)]

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use num_traits::ToPrimitive;

use crate::blessed::PreludeIds;
use crate::context::Context;
use crate::declarations::Data;
use crate::diagnostic::{Diagnostic, Refusal};
use crate::first_order::{self as d, Expr, ExprKind};
use crate::hir::LocalId;
use crate::specialize::{FunctionKey, Instance, Pattern, Signature, Split, Type};
use crate::{ModuleId, Symbol, Symbols};

#[derive(Clone, Debug)]
pub(crate) struct Program {
    pub(crate) entry: Option<FunctionKey>,
    pub(crate) functions: Vec<Function>,
    pub(crate) data: HashMap<Symbol, Data>,
    /// Where each definition is written, which a refusal naming one by
    /// name points at.
    pub(crate) written: HashMap<Symbol, (ModuleId, crate::ast::Span)>,
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
pub(crate) fn compile(program: d::Program, cx: &Context) -> Result<Program, Diagnostic> {
    compiled(program, &cx.prelude, &cx.symbols).map_err(|refusal| cx.told(refusal))
}

fn compiled(
    program: d::Program,
    prelude: &PreludeIds,
    symbols: &Symbols,
) -> Result<Program, Refusal> {
    let joins = Joins::default();
    let compiler = Compiler {
        data: &program.data,
        prelude,
        symbols,
        run_out: RunOut::Refused,
        joins: &joins,
        clauses: None,
    };
    let mut functions: Vec<Function> = program
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
                                body: compiler.tail_body(clause.body, &function.key)?,
                                locals: HashMap::new(),
                            })
                        })
                        .collect::<Result<Vec<_>, Refusal>>()?;
                    let mut next = u32::try_from(subjects.len()).expect("a sane arity");
                    let planning = Compiler {
                        clauses: Some(Rc::new(Clauses::of(&function.key))),
                        ..compiler.clone()
                    };
                    Definition::Body(Box::new(planning.plan(&rows, &subjects, &mut next)?))
                }
            };
            Ok(Function {
                key: function.key,
                definition,
            })
        })
        .collect::<Result<_, Refusal>>()?;
    functions.extend(joins.functions.into_inner());
    Ok(Program {
        entry: program.entry,
        functions,
        data: program.data,
        written: program.written,
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
    /// Whether this tests a natural for a numeral anywhere, the decisions
    /// in the bodies it answers among them.
    pub(crate) fn tests_numerals(&self) -> bool {
        match self {
            Self::Unreachable { .. } => false,
            Self::Body { body, .. } => body.tests_numerals(),
            Self::Numeral { .. } => true,
            Self::Match { arms, .. } => arms.iter().any(|arm| arm.decision.tests_numerals()),
            Self::Record { decision, .. } | Self::Split { decision, .. } => {
                decision.tests_numerals()
            }
            Self::Let {
                subject, decision, ..
            } => subject.tests_numerals() || decision.tests_numerals(),
            Self::Guard {
                condition,
                otherwise,
                answer,
                ..
            } => {
                condition.tests_numerals() || otherwise.tests_numerals() || answer.tests_numerals()
            }
        }
    }
}

impl Body {
    /// Whether a decision this body binds tests for a numeral.
    fn tests_numerals(&self) -> bool {
        self.bindings.iter().any(|binding| match &binding.value {
            Bound::Value(_) => false,
            Bound::If { yes, no, .. } => yes.tests_numerals() || no.tests_numerals(),
            Bound::Match { decision, .. } => decision.tests_numerals(),
        })
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

/// The largest numeral a column also taking successors apart is taken apart
/// for. See [`Compiler::numeral_column`].
const PEELED_SUCCESSORS: u8 = 64;

#[derive(Clone)]
struct Compiler<'a> {
    data: &'a HashMap<Symbol, Data>,
    prelude: &'a PreludeIds,
    symbols: &'a Symbols,
    run_out: RunOut,
    joins: &'a Joins,
    /// Where the rows planned are a function's own clauses; see
    /// [`Compiler::fallthrough`].
    clauses: Option<Rc<Clauses>>,
}

/// A function's clauses as they are planned: the function, and the type of
/// each value planning has taken apart, which a join point it makes is
/// handed.
struct Clauses {
    function: FunctionKey,
    types: RefCell<HashMap<Value, Type>>,
}

impl Clauses {
    fn of(function: &FunctionKey) -> Self {
        Self {
            function: function.clone(),
            types: RefCell::new(HashMap::new()),
        }
    }
}

/// The join points made while compiling, and how many there are; the
/// locals hoisting and loops make, numbered across the whole program so
/// that none a function is handed is made again in it; and the loops whose
/// rounds are being compiled, innermost last.
#[derive(Default)]
struct Joins {
    functions: RefCell<Vec<Function>>,
    made: Cell<u32>,
    hoisted: Cell<u32>,
    looped: Cell<u32>,
    exits: RefCell<Vec<Exits>>,
}

/// Where a loop's `continue` and `break` go: the round's function, with
/// what it reads beside what the loop carries and, for `for`, the rest of
/// the list; and the function of the lines after it, with what they read.
#[derive(Clone)]
struct Exits {
    round: FunctionKey,
    round_reads: Vec<(LocalId, Type)>,
    rest_of_list: Option<(LocalId, Type)>,
    after: FunctionKey,
    after_reads: Vec<(LocalId, Type)>,
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
    /// A body the function answers, made so that each branch that may
    /// leave answers it too; see [`Self::joined`].
    fn tail_body(&self, body: d::Body, key: &FunctionKey) -> Result<Body, Refusal> {
        self.tail_body_then(body, key, None)
    }

    /// [`Self::tail_body`], its answer handed to `then` where there is one.
    fn tail_body_then(
        &self,
        body: d::Body,
        key: &FunctionKey,
        then: Option<&(FunctionKey, Vec<(LocalId, Type)>)>,
    ) -> Result<Body, Refusal> {
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
        let mut body = exported(self.hoisted(body));
        if let Some((then, reads)) = then {
            body.result = handed_on(body.result, then, reads, key);
        }
        let body = self.joined(body, key)?;
        self.compiled(body)
    }

    /// [`hoisted`], numbering what it makes across the program.
    fn hoisted(&self, body: d::Body) -> d::Body {
        let mut fresh = self.joins.hoisted.get();
        let body = hoisted(body, &mut fresh);
        self.joins.hoisted.set(fresh);
        body
    }

    /// A local no clause has, for a loop's element and the rest of its list.
    fn loop_local(&self) -> LocalId {
        let made = self.joins.looped.get();
        self.joins.looped.set(made + 1);
        LocalId((1 << 31) + made)
    }

    /// A function key for what lowering makes of `key`'s body.
    fn made_key(&self, key: &FunctionKey, parameters: Vec<Type>) -> FunctionKey {
        let made = self.joins.made.get();
        self.joins.made.set(made + 1);
        FunctionKey {
            name: key.name,
            signature: Signature {
                parameters,
                result: key.signature.result.clone(),
            },
            instance: Instance::Join(made),
        }
    }

    /// A loop answering the function: the lines after it a function of what
    /// it carries out and what they read, `after`, whose answer goes on to
    /// `then` where there is one; the round a function of what it carries
    /// in, what it and `after` read, and for `for` the rest of the list,
    /// calling itself for the next round and `after` once the loop ends.
    /// What stands for the loop is a call of the round.
    fn looped(
        &self,
        looped: d::Loop,
        (module, span): (ModuleId, crate::ast::Span),
        key: &FunctionKey,
        then: Option<&(FunctionKey, Vec<(LocalId, Type)>)>,
    ) -> Result<Expr, Refusal> {
        let answer = key.signature.result.as_ref().clone();
        let d::Loop {
            carried,
            head,
            body,
            rest,
        } = looped;
        let local = |local: LocalId, ty: &Type| Expr {
            module,
            span,
            ty: ty.clone(),
            kind: ExprKind::Local(local),
        };
        let types: Vec<Type> = carried
            .iter()
            .map(|(initial, _, _)| initial.ty.clone())
            .collect();
        let afters: Vec<LocalId> = carried.iter().map(|(_, _, after)| *after).collect();
        let withins: Vec<LocalId> = carried.iter().map(|(_, within, _)| *within).collect();

        let mut after_reads = free_in(&rest, &afters.iter().copied().collect());
        // A `continue` or `break` of the loop around this one, written
        // after it, hands on what that loop's functions read.
        let outer = self.exit_reads();
        for read in then.iter().flat_map(|(_, reads)| reads).chain(&outer) {
            if !afters.contains(&read.0) && !after_reads.contains(read) {
                after_reads.push(read.clone());
            }
        }
        let after = self.made_key(
            key,
            types
                .iter()
                .cloned()
                .chain(after_reads.iter().map(|(_, ty)| ty.clone()))
                .collect(),
        );
        let after_body = self.tail_body_then(rest, key, then)?;
        self.made(
            after.clone(),
            after_body,
            afters
                .iter()
                .chain(after_reads.iter().map(|(read, _)| read)),
        );

        let ended = Expr {
            module,
            span,
            ty: answer.clone(),
            kind: ExprKind::Break(
                withins
                    .iter()
                    .zip(&types)
                    .map(|(within, ty)| local(*within, ty))
                    .collect(),
            ),
        };
        let ended = block(
            d::Body {
                bindings: Vec::new(),
                result: ended,
            },
            &answer,
        );
        let (decided, walking, list) = match head {
            d::LoopHead::While(condition) => (
                ExprKind::If(
                    Box::new(condition),
                    Box::new(block(body, &answer)),
                    Box::new(ended),
                ),
                None,
                None,
            ),
            d::LoopHead::For(pattern, list) => {
                let element = match &list.ty {
                    Type::Named(_, arguments) if arguments.len() == 1 => arguments[0].clone(),
                    _ => return Err(error("a `for` loop walks a list")),
                };
                let (walked, taken, more) =
                    (self.loop_local(), self.loop_local(), self.loop_local());
                let mut round = d::Body {
                    bindings: vec![d::Binding {
                        pattern,
                        value: local(taken, &element),
                    }],
                    result: body.result,
                };
                round.bindings.extend(body.bindings);
                let arms = vec![
                    d::Arm {
                        rows: vec![(
                            Pattern::List(
                                vec![Pattern::Bind(taken)],
                                Some(Box::new(Pattern::Bind(more))),
                            ),
                            None,
                        )],
                        body: block(round, &answer),
                    },
                    d::Arm {
                        rows: vec![(Pattern::List(Vec::new(), None), None)],
                        body: ended,
                    },
                ];
                (
                    ExprKind::Match(Box::new(local(walked, &list.ty)), arms),
                    Some((walked, more, list.ty.clone())),
                    Some(list),
                )
            }
        };
        let round_body = d::Body {
            bindings: Vec::new(),
            result: Expr {
                module,
                span,
                ty: answer.clone(),
                kind: decided,
            },
        };
        let mut own: HashSet<LocalId> = withins.iter().copied().collect();
        own.extend(
            walking
                .iter()
                .flat_map(|(walked, more, _)| [*walked, *more]),
        );
        let mut round_reads = free_in(&round_body, &own);
        for read in &after_reads {
            if !round_reads.contains(read) {
                round_reads.push(read.clone());
            }
        }
        let mut parameters = types;
        parameters.extend(round_reads.iter().map(|(_, ty)| ty.clone()));
        parameters.extend(walking.iter().map(|(_, _, ty)| ty.clone()));
        let round = self.made_key(key, parameters);
        self.joins.exits.borrow_mut().push(Exits {
            round: round.clone(),
            round_reads: round_reads.clone(),
            rest_of_list: walking.as_ref().map(|(_, more, ty)| (*more, ty.clone())),
            after,
            after_reads,
        });
        let compiled = self.tail_body(round_body, key);
        self.joins.exits.borrow_mut().pop();
        self.made(
            round.clone(),
            compiled?,
            withins
                .iter()
                .chain(round_reads.iter().map(|(read, _)| read))
                .chain(walking.iter().map(|(walked, _, _)| walked)),
        );
        let mut arguments: Vec<Expr> = carried.into_iter().map(|(initial, _, _)| initial).collect();
        arguments.extend(round_reads.iter().map(|(read, ty)| local(*read, ty)));
        arguments.extend(list);
        Ok(Expr {
            module,
            span,
            ty: answer,
            kind: ExprKind::DirectCall(round, arguments),
        })
    }

    /// What a `continue` or `break` of the innermost loop hands on beside
    /// what the loop carries: what its round and the lines after it read,
    /// and the rest of the list a `for` walks.
    fn exit_reads(&self) -> Vec<(LocalId, Type)> {
        let exits = self.joins.exits.borrow();
        let Some(exits) = exits.last() else {
            return Vec::new();
        };
        exits
            .round_reads
            .iter()
            .chain(&exits.rest_of_list)
            .chain(&exits.after_reads)
            .cloned()
            .collect()
    }

    /// A function lowering made, `body` with `parameters` as its locals.
    fn made<'p>(
        &self,
        key: FunctionKey,
        body: Body,
        parameters: impl Iterator<Item = &'p LocalId>,
    ) {
        let locals = parameters
            .enumerate()
            .map(|(at, local)| (*local, Value(u32::try_from(at).expect("a sane arity"))))
            .collect();
        self.joins.functions.borrow_mut().push(Function {
            key,
            definition: Definition::Body(Box::new(Decision::Body { body, locals })),
        });
    }

    /// A body's answer where it is a `continue` or a `break`: a call of the
    /// innermost loop's round, or of the lines after it.
    fn left(&self, answer: Expr) -> Expr {
        let (values, continuing) = match answer.kind {
            ExprKind::Continue(values) => (values, true),
            ExprKind::Break(values) => (values, false),
            kind => return Expr { kind, ..answer },
        };
        let exits = self.joins.exits.borrow();
        let exits = exits
            .last()
            .expect("resolution keeps `continue` and `break` in loops");
        let read = |(local, ty): &(LocalId, Type)| Expr {
            module: answer.module,
            span: answer.span,
            ty: ty.clone(),
            kind: ExprKind::Local(*local),
        };
        let (callee, mut arguments) = if continuing {
            let mut arguments = values;
            arguments.extend(exits.round_reads.iter().map(read));
            if let Some((more, ty)) = &exits.rest_of_list {
                arguments.push(read(&(*more, ty.clone())));
            }
            (exits.round.clone(), arguments)
        } else {
            (exits.after.clone(), values)
        };
        if !continuing {
            arguments.extend(exits.after_reads.iter().map(read));
        }
        Expr {
            kind: ExprKind::DirectCall(callee, arguments),
            ..answer
        }
    }

    /// A hoisted body the function answers, each `if` or arms of it whose
    /// branches may leave, by `?` or `return`, made to answer the function:
    /// where lines follow it, those lines become a join point, a function
    /// of the branch's value and what they read, which each branch going
    /// on calls; a branch leaving answers the function itself. The same is
    /// made of each branch, and of the join point, in turn.
    fn joined(&self, mut body: d::Body, key: &FunctionKey) -> Result<d::Body, Refusal> {
        let Some(at) = body
            .bindings
            .iter()
            .position(|binding| branches_leave(&binding.value))
        else {
            return Ok(body);
        };
        let answer = key.signature.result.as_ref().clone();
        let rest = d::Body {
            bindings: body.bindings.split_off(at + 1),
            result: body.result,
        };
        let construct = body.bindings.pop().expect("the binding found");
        let Pattern::Bind(local) = construct.pattern else {
            unreachable!("hoisting binds each `if` and arms to a local of its own")
        };
        let last = rest.bindings.is_empty()
            && matches!(rest.result.kind, ExprKind::Local(answered) if answered == local);
        let join = if last {
            None
        } else {
            let mut live = live_in(&rest, local);
            // A round's lines that go on to the next round or leave the
            // loop hand on what its round or the lines after it read, which
            // the join point must be given.
            if exits_loop(&rest) {
                for read in self.exit_reads() {
                    if !live.contains(&read) {
                        live.push(read);
                    }
                }
            }
            let mut parameters = vec![construct.value.ty.clone()];
            parameters.extend(live.iter().map(|(_, ty)| ty.clone()));
            let made = self.joins.made.get();
            self.joins.made.set(made + 1);
            let join = FunctionKey {
                name: key.name,
                signature: Signature {
                    parameters,
                    result: Box::new(answer.clone()),
                },
                instance: Instance::Join(made),
            };
            let rest = self.joined(rest, key)?;
            let locals = std::iter::once(local)
                .chain(live.iter().map(|(local, _)| *local))
                .enumerate()
                .map(|(at, local)| (local, Value(u32::try_from(at).expect("a sane arity"))))
                .collect();
            let body = self.compiled(rest)?;
            self.joins.functions.borrow_mut().push(Function {
                key: join.clone(),
                definition: Definition::Body(Box::new(Decision::Body { body, locals })),
            });
            Some((join, live))
        };
        let (module, span) = (construct.value.module, construct.value.span);
        let value = match construct.value.kind {
            ExprKind::Loop(looped) => self.looped(*looped, (module, span), key, join.as_ref())?,
            kind => self.answering(
                Expr {
                    kind,
                    ..construct.value
                },
                &answer,
                join.as_ref(),
                key,
            )?,
        };
        body.bindings.push(d::Binding {
            pattern: Pattern::Bind(local),
            value,
        });
        body.result = Expr {
            module,
            span,
            ty: answer,
            kind: ExprKind::Local(local),
        };
        Ok(body)
    }

    /// An `if` or arms made to answer the function: each branch's body
    /// [`Self::joined`], its answer handed to `join` where there is one, and
    /// a `return` answering where it stands.
    fn answering(
        &self,
        construct: Expr,
        answer: &Type,
        join: Option<&(FunctionKey, Vec<(LocalId, Type)>)>,
        key: &FunctionKey,
    ) -> Result<Expr, Refusal> {
        let branch = |branch: Expr| -> Result<Expr, Refusal> {
            let ExprKind::Block(body) = branch.kind else {
                unreachable!("hoisting makes each branch a block")
            };
            let mut body = *body;
            body.result = match body.result.kind {
                ExprKind::Return(value) => *value,
                // Leaving a round or the loop, which the loop's own lowering
                // turns into a call.
                kind @ (ExprKind::Continue(_) | ExprKind::Break(_)) => Expr {
                    kind,
                    ..body.result
                },
                kind => {
                    let result = Expr {
                        kind,
                        ..body.result
                    };
                    match join {
                        Some((join, live)) => {
                            let mut arguments = vec![result];
                            arguments.extend(live.iter().map(|(local, ty)| Expr {
                                module: branch.module,
                                span: branch.span,
                                ty: ty.clone(),
                                kind: ExprKind::Local(*local),
                            }));
                            Expr {
                                module: branch.module,
                                span: branch.span,
                                ty: answer.clone(),
                                kind: ExprKind::DirectCall(join.clone(), arguments),
                            }
                        }
                        None => result,
                    }
                }
            };
            Ok(Expr {
                module: branch.module,
                span: branch.span,
                ty: answer.clone(),
                kind: ExprKind::Block(Box::new(self.joined(body, key)?)),
            })
        };
        let kind = match construct.kind {
            ExprKind::If(condition, yes, no) => {
                ExprKind::If(condition, Box::new(branch(*yes)?), Box::new(branch(*no)?))
            }
            ExprKind::Match(subject, arms) => ExprKind::Match(
                subject,
                arms.into_iter()
                    .map(|arm| {
                        Ok(d::Arm {
                            rows: arm.rows,
                            body: branch(arm.body)?,
                        })
                    })
                    .collect::<Result<_, Refusal>>()?,
            ),
            _ => unreachable!("only an `if` or arms has branches that leave"),
        };
        Ok(Expr {
            module: construct.module,
            span: construct.span,
            ty: answer.clone(),
            kind,
        })
    }

    fn body(&self, body: d::Body) -> Result<Body, Refusal> {
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
    ) -> Result<Bound, Refusal> {
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

    /// `subject is ( arms )`, as a decision on the subject: a row for each
    /// alternative of each arm, in order, each answering its arm's body.
    /// Checking found the arms cover every value.
    fn arms(&self, subject: Expr, arms: Vec<d::Arm>) -> Result<Bound, Refusal> {
        let subjects = [Subject {
            value: Value(0),
            ty: subject.ty.clone(),
        }];
        let mut rows = Vec::new();
        for arm in arms {
            let ExprKind::Block(body) = arm.body.kind else {
                unreachable!("hoisting makes each arm a block")
            };
            let body = self.compiled(*body)?;
            for (pattern, guard) in arm.rows {
                rows.push(Row {
                    patterns: vec![pattern],
                    guard: guard
                        .map(|guard| asked(guard, self.prelude))
                        .unwrap_or_default(),
                    body: body.clone(),
                    locals: HashMap::new(),
                });
            }
        }
        let decision = self.plan(&rows, &subjects, &mut 1)?;
        Ok(Bound::Match {
            subject,
            decision: Box::new(decision),
        })
    }

    /// A body [`hoisted`] already, whose `if`s each stand alone on a line,
    /// their branches hoisted too.
    fn compiled(&self, body: d::Body) -> Result<Body, Refusal> {
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
                    ExprKind::Match(subject, arms) => self.arms(*subject, arms)?,
                    _ => Bound::Value(binding.value),
                };
                Ok(Binding { unpack, value })
            })
            .collect::<Result<_, Refusal>>()?;
        Ok(Body {
            bindings,
            result: self.left(body.result),
        })
    }

    fn unpack(&self, pattern: Pattern, ty: &Type) -> Result<Unpack, Refusal> {
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
                        self.symbols.spelling(constructor)
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
    ) -> Result<Decision, Refusal> {
        if let Some(clauses) = &self.clauses {
            let mut types = clauses.types.borrow_mut();
            for subject in subjects {
                types
                    .entry(subject.value)
                    .or_insert_with(|| subject.ty.clone());
            }
        }
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
                either.extend(self.rest(&rows[1..], subjects)?);
                return self.plan(&either, subjects, next);
            }
            let rest = self.rest(&rows[1..], subjects)?;
            let otherwise = self.plan(&rest, subjects, next)?;
            let locals = first.locals.clone();
            let mut going_on = vec![first];
            going_on.extend(rest);
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
            // Where rows below take successors apart, what a test found is
            // not known to them: a way taking `0` apart, past a test that
            // it is not `0`, is one no value goes, as the clauses were found
            // to cover every value.
            let taken_apart = rows
                .iter()
                .any(|row| matches!(row.patterns[column], Pattern::Constructor(..)));
            let below = if taken_apart {
                Self {
                    run_out: RunOut::Unreachable(subject.clone()),
                    ..self.clone()
                }
            } else {
                self.clone()
            };
            return Ok(Decision::Numeral {
                subject: subject.value,
                number,
                equal: Box::new(below.plan(&equal, subjects, next)?),
                otherwise: Box::new(below.plan(&otherwise, subjects, next)?),
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
    ) -> Result<Decision, Refusal> {
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
        for mut row in self.rest(&rows[1..], subjects)? {
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

    /// The rows tried where the row above them fails: themselves, or where
    /// they are a function's clauses, one row taking anything that calls a
    /// join point planned from them, handed each value matched and each
    /// one they have bound. A row's guard, a test in it, or a list's end
    /// failing has every row below it planned again on each way it fails,
    /// and each of those again, which a join point plans once. Rows no
    /// more than a catch-all are kept, as copying one copies nothing more.
    fn rest(&self, rest: &[Row], subjects: &[Subject]) -> Result<Vec<Row>, Refusal> {
        let Some(clauses) = &self.clauses else {
            return Ok(rest.to_vec());
        };
        let plain = |row: &Row| row.guard.is_empty() && row.patterns.iter().all(irrefutable);
        if rest.is_empty() || matches!(rest, [only] if plain(only)) {
            return Ok(rest.to_vec());
        }
        let mut handed: Vec<(Value, Type)> = subjects
            .iter()
            .map(|subject| (subject.value, subject.ty.clone()))
            .collect();
        let mut bound: Vec<Value> = rest
            .iter()
            .flat_map(|row| row.locals.values().copied())
            .filter(|value| !handed.iter().any(|(handed, _)| handed == value))
            .collect();
        bound.sort_unstable_by_key(|value| value.0);
        bound.dedup();
        {
            let types = clauses.types.borrow();
            for value in bound {
                let ty = types
                    .get(&value)
                    .cloned()
                    .ok_or_else(|| error("a value a row bound has a type"))?;
                handed.push((value, ty));
            }
        }
        let renumbered: HashMap<Value, Value> = handed
            .iter()
            .enumerate()
            .map(|(at, (value, _))| (*value, Value(u32::try_from(at).expect("a sane arity"))))
            .collect();
        let join_subjects: Vec<Subject> = subjects
            .iter()
            .map(|subject| Subject {
                value: renumbered[&subject.value],
                ty: subject.ty.clone(),
            })
            .collect();
        let join_rows: Vec<Row> = rest
            .iter()
            .map(|row| Row {
                locals: row
                    .locals
                    .iter()
                    .map(|(local, value)| (*local, renumbered[value]))
                    .collect(),
                ..row.clone()
            })
            .collect();
        let key = self.made_key(
            &clauses.function,
            handed.iter().map(|(_, ty)| ty.clone()).collect(),
        );
        // The rows are tried only where the rows above failed, which this
        // plan does not know: a way it leaves for no row is one the rows
        // above took, as the clauses were found to cover every value.
        let run_out = join_subjects.first().map_or_else(
            || self.run_out.clone(),
            |subject| RunOut::Unreachable(subject.clone()),
        );
        let joined = Clauses::of(&clauses.function);
        joined.types.borrow_mut().extend(
            handed
                .iter()
                .map(|(value, ty)| (renumbered[value], ty.clone())),
        );
        let planning = Self {
            clauses: Some(Rc::new(joined)),
            run_out,
            ..self.clone()
        };
        let mut next = u32::try_from(handed.len()).expect("a sane arity");
        let decision = planning.plan(&join_rows, &join_subjects, &mut next)?;
        self.joins.functions.borrow_mut().push(Function {
            key: key.clone(),
            definition: Definition::Body(Box::new(decision)),
        });
        let (module, span) = (rest[0].body.result.module, rest[0].body.result.span);
        let mut locals = HashMap::new();
        let arguments = handed
            .iter()
            .map(|(value, ty)| {
                let local = self.loop_local();
                locals.insert(local, *value);
                Expr {
                    module,
                    span,
                    ty: ty.clone(),
                    kind: ExprKind::Local(local),
                }
            })
            .collect();
        let call = Expr {
            module,
            span,
            ty: clauses.function.signature.result.as_ref().clone(),
            kind: ExprKind::DirectCall(key, arguments),
        };
        Ok(vec![Row {
            patterns: vec![Pattern::Wild; subjects.len()],
            guard: Vec::new(),
            body: Body {
                bindings: Vec::new(),
                result: call,
            },
            locals,
        }])
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
    ) -> Result<Decision, Refusal> {
        let subject = &subjects[column];
        let count = split.last.len();
        let mut fresh = || {
            let value = Value(*next);
            *next = next.checked_add(1).expect("fewer than 2^32 plan values");
            value
        };
        let (front, back) = (fresh(), fresh());
        // Where the first row is split here, every way its end does not
        // match goes on to the rows below it: one join point, not a copy of
        // them for each way.
        let rows = match rows.split_first() {
            Some((first, below))
                if ending(&first.patterns[column]).is_some_and(|own| own.last.len() == count) =>
            {
                let mut rows = vec![first.clone()];
                rows.extend(self.rest(below, subjects)?);
                rows
            }
            _ => rows.to_vec(),
        };
        let mut specialized = Vec::with_capacity(rows.len());
        for row in &rows {
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
    /// holds; up to [`PEELED_SUCCESSORS`]. Past that, taking a numeral
    /// apart is a match for each successor in it, for each row, so its
    /// numerals are tested first, and the rows taking successors apart are
    /// tried on each way as rows taking anything are.
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
        let mut peeled = PEELED_NUMERALS;
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
                Pattern::Constructor(..) => peeled = PEELED_SUCCESSORS,
                _ => return None,
            }
        }
        first.filter(|_| largest > num_bigint::BigUint::from(peeled))
    }

    fn normalize_pattern(&self, pattern: Pattern, expected: &Type) -> Result<Pattern, Refusal> {
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
    ) -> Result<Pattern, Refusal> {
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

    fn natural_pattern(&self, magnitude: &num_bigint::BigUint) -> Result<Pattern, Refusal> {
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

/// `body` with each `if` or arms in it that no branch leaves handing out,
/// beside its value, what every branch binds last and the lines after it
/// read: the names a branch assigned, which resolution bound again at the
/// end of each branch. Its branches answer a tuple, which its binding takes
/// apart. Inner ones are made first.
fn exported(mut body: d::Body) -> d::Body {
    let mut read = HashSet::new();
    let reads = |expression: &Expr, read: &mut HashSet<LocalId>| {
        expression.for_each_within(&mut |inner| {
            if let ExprKind::Local(local) = inner.kind {
                read.insert(local);
            }
        });
    };
    reads(&body.result, &mut read);
    let mut after = vec![HashSet::new(); body.bindings.len()];
    for (at, binding) in body.bindings.iter().enumerate().rev() {
        after[at].clone_from(&read);
        reads(&binding.value, &mut read);
    }
    body.bindings = body
        .bindings
        .into_iter()
        .zip(after)
        .map(|(binding, after)| handed_out(binding, &after))
        .collect();
    body
}

/// One binding of [`exported`], its value's branches made first.
fn handed_out(binding: d::Binding, after: &HashSet<LocalId>) -> d::Binding {
    let inner = |branch: Expr| match branch.kind {
        ExprKind::Block(body) => Expr {
            kind: ExprKind::Block(Box::new(exported(*body))),
            ..branch
        },
        kind => Expr { kind, ..branch },
    };
    let value = binding.value;
    let value = match value.kind {
        ExprKind::If(condition, yes, no) => Expr {
            kind: ExprKind::If(condition, Box::new(inner(*yes)), Box::new(inner(*no))),
            ..value
        },
        ExprKind::Match(subject, arms) => Expr {
            kind: ExprKind::Match(
                subject,
                arms.into_iter()
                    .map(|arm| d::Arm {
                        rows: arm.rows,
                        body: inner(arm.body),
                    })
                    .collect(),
            ),
            ..value
        },
        kind => {
            return d::Binding {
                pattern: binding.pattern,
                value: Expr { kind, ..value },
            };
        }
    };
    if branches_leave(&value) {
        return d::Binding {
            pattern: binding.pattern,
            value,
        };
    }
    let branches: Vec<&Expr> = match &value.kind {
        ExprKind::If(_, yes, no) => vec![yes, no],
        ExprKind::Match(_, arms) => arms.iter().map(|arm| &arm.body).collect(),
        _ => unreachable!("matched above"),
    };
    let bound_last = |branch: &Expr| -> BTreeMap<LocalId, Type> {
        let ExprKind::Block(body) = &branch.kind else {
            return BTreeMap::new();
        };
        body.bindings
            .iter()
            .filter_map(|binding| match binding.pattern {
                Pattern::Bind(local) => Some((local, binding.value.ty.clone())),
                _ => None,
            })
            .collect()
    };
    let mut handed: BTreeMap<LocalId, Type> = branches
        .first()
        .map(|branch| bound_last(branch))
        .unwrap_or_default();
    for branch in &branches[1..] {
        let bound = bound_last(branch);
        handed.retain(|local, _| bound.contains_key(local));
    }
    handed.retain(|local, _| after.contains(local));
    if handed.is_empty() {
        return d::Binding {
            pattern: binding.pattern,
            value,
        };
    }
    let mut members = vec![value.ty.clone()];
    members.extend(handed.values().cloned());
    let tuple = Type::Tuple(members);
    let answering = |branch: Expr| {
        let ExprKind::Block(mut body) = branch.kind else {
            unreachable!("hoisting makes each branch a block")
        };
        let mut members = vec![body.result];
        members.extend(handed.iter().map(|(local, ty)| Expr {
            module: branch.module,
            span: branch.span,
            ty: ty.clone(),
            kind: ExprKind::Local(*local),
        }));
        body.result = Expr {
            module: branch.module,
            span: branch.span,
            ty: tuple.clone(),
            kind: ExprKind::Tuple(members),
        };
        Expr {
            ty: tuple.clone(),
            kind: ExprKind::Block(body),
            ..branch
        }
    };
    let kind = match value.kind {
        ExprKind::If(condition, yes, no) => ExprKind::If(
            condition,
            Box::new(answering(*yes)),
            Box::new(answering(*no)),
        ),
        ExprKind::Match(subject, arms) => ExprKind::Match(
            subject,
            arms.into_iter()
                .map(|arm| d::Arm {
                    rows: arm.rows,
                    body: answering(arm.body),
                })
                .collect(),
        ),
        _ => unreachable!("matched above"),
    };
    let mut parts = vec![binding.pattern];
    parts.extend(handed.keys().map(|local| Pattern::Bind(*local)));
    d::Binding {
        pattern: Pattern::Product(parts),
        value: Expr {
            ty: tuple.clone(),
            kind,
            ..value
        },
    }
}

/// `body` as a block of type `ty`.
fn block(body: d::Body, ty: &Type) -> Expr {
    Expr {
        module: body.result.module,
        span: body.result.span,
        ty: ty.clone(),
        kind: ExprKind::Block(Box::new(body)),
    }
}

/// `answer` handed to `then`, with what it reads beside.
fn handed_on(
    answer: Expr,
    then: &FunctionKey,
    reads: &[(LocalId, Type)],
    key: &FunctionKey,
) -> Expr {
    let (module, span) = (answer.module, answer.span);
    let mut arguments = vec![answer];
    arguments.extend(reads.iter().map(|(local, ty)| Expr {
        module,
        span,
        ty: ty.clone(),
        kind: ExprKind::Local(*local),
    }));
    Expr {
        module,
        span,
        ty: key.signature.result.as_ref().clone(),
        kind: ExprKind::DirectCall(then.clone(), arguments),
    }
}

/// Whether `value` is an `if` or arms with a branch that may leave the
/// function, by `?` or `return`, anywhere inside it.
fn branches_leave(value: &Expr) -> bool {
    match &value.kind {
        // A loop always answers the function, its rounds and what follows
        // it calling one another.
        ExprKind::Loop(_) => true,
        ExprKind::If(_, yes, no) => leaves(yes) || leaves(no),
        ExprKind::Match(_, arms) => arms.iter().any(|arm| leaves(&arm.body)),
        _ => false,
    }
}

/// Whether a `?` or a `return` is anywhere in `expression`.
fn leaves(expression: &Expr) -> bool {
    let mut found = false;
    expression.for_each_within(&mut |inner| {
        found |= matches!(
            inner.kind,
            ExprKind::Try(_)
                | ExprKind::Return(_)
                | ExprKind::Continue(_)
                | ExprKind::Break(_)
                | ExprKind::Loop(_)
        );
    });
    found
}

/// Whether a `continue` or a `break` is anywhere in `body`.
fn exits_loop(body: &d::Body) -> bool {
    let mut found = false;
    for expression in body.exprs() {
        expression.for_each_within(&mut |inner| {
            found |= matches!(inner.kind, ExprKind::Continue(_) | ExprKind::Break(_));
        });
    }
    found
}

/// What `rest` reads that it does not bind, but `answered`, each at its
/// type, in order: a join point's parameters after the branch's value.
fn live_in(rest: &d::Body, answered: LocalId) -> Vec<(LocalId, Type)> {
    free_in(rest, &HashSet::from([answered]))
}

/// What `body` reads that neither it binds nor `own` holds, each at its
/// type, in order.
fn free_in(body: &d::Body, own: &HashSet<LocalId>) -> Vec<(LocalId, Type)> {
    let mut read = BTreeMap::new();
    let mut bound = own.clone();
    for binding in &body.bindings {
        binding.pattern.for_each_bound(&mut |local| {
            bound.insert(local);
        });
    }
    for expression in body.exprs() {
        expression.for_each_within(&mut |inner| {
            if let ExprKind::Local(local) = inner.kind {
                read.entry(local).or_insert_with(|| inner.ty.clone());
            }
            inner.for_each_bound(|local| {
                bound.insert(local);
            });
        });
    }
    read.into_iter()
        .filter(|(local, _)| !bound.contains(local))
        .collect()
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
        kind @ (ExprKind::Local(_)
        | ExprKind::Natural(_)
        | ExprKind::Bytes(_)
        | ExprKind::Continue(_)
        | ExprKind::Break(_)) => kind,
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
        ExprKind::Return(value) => ExprKind::Return(one(value)),
        // What goes into a loop is worked out where it stands; the rest is
        // worked out where lowering makes the loop's functions.
        ExprKind::Loop(looped) => {
            let mut looped = *looped;
            for (initial, _, _) in &mut looped.carried {
                *initial = tested(initial.clone(), prelude);
            }
            if let d::LoopHead::For(_, list) = &mut looped.head {
                *list = tested(list.clone(), prelude);
            }
            ExprKind::Loop(Box::new(looped))
        }
        // A guard is asked a part at a time where its arm is planned.
        ExprKind::Match(value, arms) => ExprKind::Match(
            one(value),
            arms.into_iter()
                .map(|arm| d::Arm {
                    rows: arm.rows,
                    body: tested(arm.body, prelude),
                })
                .collect(),
        ),
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
/// place it is reached from, where it is no more than a value; one that
/// branches itself is written once, after the condition is worked out
/// (see [`outcome`]), as copying it would copy what it holds as often as
/// the chains before it have parts.
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
    let copied = match &condition.kind {
        ExprKind::DirectCall(key, _) if key.name == prelude.bool_and => Some(&no),
        ExprKind::DirectCall(key, _) if key.name == prelude.bool_or => Some(&yes),
        _ => None,
    };
    if copied.is_some_and(branches) {
        return outcome(condition, yes, no, prelude);
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

/// `if condition then yes else no`, where the condition is a chain of `&`
/// and `|` holding a test: the condition worked out first, to one tag
/// holding what its tests bound that `yes` reads, or another saying it
/// failed, and that tag taken apart once, `yes` in one arm and `no` in the
/// other. Only the tags are copied along the chain.
fn outcome(condition: Expr, yes: Expr, no: Expr, prelude: &PreludeIds) -> Expr {
    let (module, span) = (condition.module, condition.span);
    let bound = bound_by(&condition, prelude);
    let mut read: Vec<(LocalId, Type)> = Vec::new();
    yes.for_each_within(&mut |expression| {
        if let ExprKind::Local(local) = expression.kind
            && bound.contains(&local)
            && !read.iter().any(|(seen, _)| *seen == local)
        {
            read.push((local, expression.ty.clone()));
        }
    });
    let (held, failed) = (prelude.bool_true, prelude.bool_false);
    let mut tags = vec![
        (held, read.iter().map(|(_, ty)| ty.clone()).collect()),
        (failed, Vec::new()),
    ];
    tags.sort_by_key(|(label, _)| *label);
    let ty = Type::Variants(tags);
    let tag = |label, fields| Expr {
        module,
        span,
        ty: ty.clone(),
        kind: ExprKind::Construct(label, fields),
    };
    let reads = read
        .iter()
        .map(|(local, ty)| Expr {
            module,
            span,
            ty: ty.clone(),
            kind: ExprKind::Local(*local),
        })
        .collect();
    let chosen = branched(
        condition,
        tag(held, reads),
        tag(failed, Vec::new()),
        prelude,
    );
    let holding = read
        .iter()
        .map(|(local, _)| Pattern::Bind(*local))
        .collect();
    Expr {
        module: yes.module,
        span,
        ty: yes.ty.clone(),
        kind: ExprKind::Match(
            Box::new(chosen),
            vec![
                d::Arm {
                    rows: vec![(Pattern::Constructor(held, holding), None)],
                    body: yes,
                },
                d::Arm {
                    rows: vec![(Pattern::Constructor(failed, Vec::new()), None)],
                    body: no,
                },
            ],
        ),
    }
}

/// Whether `expression` branches anywhere in it, so that copying it copies
/// more than a value.
fn branches(expression: &Expr) -> bool {
    let mut found = false;
    expression.for_each_within(&mut |part| {
        found |= matches!(
            part.kind,
            ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Loop(..) | ExprKind::Block(..)
        );
    });
    found
}

/// What a condition's tests bind on every way it holds: past an `&`, what
/// each part binds; past an `|`, what both sides bind.
fn bound_by(condition: &Expr, prelude: &PreludeIds) -> HashSet<LocalId> {
    match &condition.kind {
        ExprKind::Is(_, alternatives) => {
            let each = alternatives.iter().map(|(pattern, guard)| {
                let mut bound = HashSet::new();
                pattern.for_each_bound(&mut |local| {
                    bound.insert(local);
                });
                if let Some(guard) = guard {
                    bound.extend(bound_by(guard, prelude));
                }
                bound
            });
            intersection(each)
        }
        ExprKind::DirectCall(key, sides) if key.name == prelude.bool_and => sides
            .iter()
            .flat_map(|side| bound_by(side, prelude))
            .collect(),
        ExprKind::DirectCall(key, sides) if key.name == prelude.bool_or => {
            intersection(sides.iter().map(|side| bound_by(side, prelude)))
        }
        _ => HashSet::new(),
    }
}

fn intersection(sets: impl Iterator<Item = HashSet<LocalId>>) -> HashSet<LocalId> {
    sets.reduce(|all, next| all.intersection(&next).copied().collect())
        .unwrap_or_default()
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
        // A branch's answer, which stays where it stands.
        ExprKind::Return(value) => ExprKind::Return(Box::new(lift(*value))),
        kind @ (ExprKind::Continue(_) | ExprKind::Break(_)) => kind,
        // A loop is bound on its own line, what goes into it worked out
        // ahead of it.
        ExprKind::Loop(looped) => {
            let mut looped = *looped;
            for (initial, _, _) in &mut looped.carried {
                *initial = lift(initial.clone());
            }
            if let d::LoopHead::For(_, list) = &mut looped.head {
                *list = lift(list.clone());
            }
            let local = LocalId(u32::MAX - *fresh);
            *fresh += 1;
            bindings.push(d::Binding {
                pattern: Pattern::Bind(local),
                value: Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::Loop(Box::new(looped)),
                },
            });
            ExprKind::Local(local)
        }
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
        // As an `if`: the value worked out ahead, each arm's body a block
        // of its own, worked out only where it is chosen.
        ExprKind::Match(value, arms) => {
            let value = lift(*value);
            let arms = arms
                .into_iter()
                .map(|arm| {
                    let body = d::Body {
                        bindings: Vec::new(),
                        result: arm.body,
                    };
                    d::Arm {
                        rows: arm.rows,
                        body: Expr {
                            module: expression.module,
                            span: expression.span,
                            ty: expression.ty.clone(),
                            kind: ExprKind::Block(Box::new(hoisted(body, fresh))),
                        },
                    }
                })
                .collect();
            let local = LocalId(u32::MAX - *fresh);
            *fresh += 1;
            bindings.push(d::Binding {
                pattern: Pattern::Bind(local),
                value: Expr {
                    module: expression.module,
                    span: expression.span,
                    ty: expression.ty.clone(),
                    kind: ExprKind::Match(Box::new(value), arms),
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

fn error(message: impl Into<String>) -> Refusal {
    Refusal::from(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked() -> crate::Checked {
        let entry =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/lowering.fn");
        crate::checked_for_test(&entry)
    }

    fn row(pattern: Pattern, checked: &crate::Checked) -> Row {
        let prelude = &checked.cx.prelude;
        Row {
            patterns: vec![pattern],
            guard: Vec::new(),
            locals: HashMap::new(),
            body: Body {
                bindings: Vec::new(),
                result: Expr {
                    module: checked.program.functions[0].module,
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
        let prelude = &checked.cx.prelude;
        let compiler = Compiler {
            data: &checked.program.data,
            prelude,
            symbols: &checked.cx.symbols,
            run_out: RunOut::Refused,
            joins: &Joins::default(),
            clauses: None,
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
        let a = checked.cx.symbols.intern("a");
        let b = checked.cx.symbols.intern("b");
        let prelude = &checked.cx.prelude;
        let compiler = Compiler {
            data: &checked.program.data,
            prelude,
            symbols: &checked.cx.symbols,
            run_out: RunOut::Refused,
            joins: &Joins::default(),
            clauses: None,
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
