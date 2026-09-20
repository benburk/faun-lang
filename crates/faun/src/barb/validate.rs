//! What the tiers below are entitled to assume of a program.
//!
//! [`parse`](super::parse) refuses what it cannot read; this refuses what it
//! read and cannot mean. The two are different jobs and only one of them is
//! about text: a program built rather than written reaches here too, and
//! nothing about a builder makes a call give a name what it takes.
//!
//! Three things, and the third is the one worth the file:
//!
//! - every call and construction is saturated, and every name it reads is
//!   one something bound
//! - every match has an arm per constructor of what it takes apart, in the
//!   order the declaration gave them
//! - every definition stops, which [`stops`](super::stops) answers

use super::model::{Atom, Body, Expr, ExprId, FnId, Range};
use super::program::Program;

/// Refuse a program the tiers below could not read rightly.
///
/// # Errors
///
/// Names the first thing wrong with it.
///
/// # Panics
///
/// If the program outgrew the four billion names or arguments it may have.
pub fn validate(program: &Program) -> Result<(), String> {
    if program.entry().is_none() {
        return Err("nothing says where the program starts".to_owned());
    }
    for ty in program.types() {
        if matches!(ty.definition, super::model::TypeDefinition::Declared) {
            return Err(format!(
                "type `{}` was declared but never defined",
                program.name(ty.name)
            ));
        }
    }
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let name = program.name(program.function(id).name);
        let level = u32::try_from(program.params(id).len()).expect("a sane arity");
        shaped(program, name, body, level)?;
    }
    super::stops::stops(program)
}

/// Every term of one body: what it reads, and how much of it.
fn shaped(program: &Program, name: &str, body: Body, level: u32) -> Result<(), String> {
    let mut level = level;
    for binding in program.bindings(body.bindings) {
        term(program, name, *binding, level)?;
        level += 1;
    }
    term(program, name, body.tail, level)
}

fn term(program: &Program, name: &str, id: ExprId, level: u32) -> Result<(), String> {
    match program.expr(id) {
        Expr::Atom(atom) => bound(name, atom, level),
        Expr::Static(..) => Ok(()),
        Expr::Con(ctor, args) => {
            let fields = program.fields(ctor).len();
            let held = program.name(program.ctor(ctor).name);
            saturated(program, name, held, args, fields, level)
        }
        Expr::Call(called, args) => {
            let params = program.params(called).len();
            let held = program.name(program.function(called).name);
            saturated(program, name, held, args, params, level)
        }
        Expr::Match(scrutinee, arms) => {
            bound(name, scrutinee, level)?;
            covers(program, name, arms)?;
            for arm in program.arms(arms) {
                let fields = u32::try_from(program.fields(arm.ctor).len()).expect("a sane arity");
                shaped(program, name, arm.body, level + fields)?;
            }
            Ok(())
        }
    }
}

/// A name a term reads is one something bound: a parameter, a binding
/// before it, or a field of what an arm took apart.
fn bound(name: &str, atom: Atom, level: u32) -> Result<(), String> {
    if atom.0.0 < level {
        return Ok(());
    }
    Err(format!("{name} reads a name nothing bound"))
}

/// A call gives a name what it takes, and a constructor is given what it
/// carries. Neither is a term a tier below could read half of.
fn saturated(
    program: &Program,
    name: &str,
    held: &str,
    args: Range,
    takes: usize,
    level: u32,
) -> Result<(), String> {
    if args.len() != takes {
        return Err(format!(
            "{name} gives `{held}` {} where it takes {takes}",
            args.len()
        ));
    }
    program
        .atoms(args)
        .iter()
        .try_for_each(|atom| bound(name, *atom, level))
}

/// A match has an arm per constructor of what it takes apart, in the order
/// the declaration gave them. Exhaustive by shape rather than by checking,
/// which is what lets a tier below read the arm it wants by tag.
fn covers(program: &Program, name: &str, arms: Range) -> Result<(), String> {
    let held = program.arms(arms);
    let Some(first) = held.first() else {
        return Err(format!("{name} matches on nothing at all"));
    };
    let owner = program.ctor(first.ctor).owner;
    let ctors = program.ctors(owner).len();
    let wrong = held.len() != ctors
        || held.iter().enumerate().any(|(at, arm)| {
            let tag = u32::try_from(at).expect("a sane constructor count");
            arm.ctor != program.ctor_at(owner, tag)
        });
    if wrong {
        let owner = program.name(program.type_(owner).name);
        return Err(format!(
            "{name} matches `{owner}` with {} arms of its {ctors}",
            held.len()
        ));
    }
    Ok(())
}
