//! The order unsigned definitions are inferred in: the strongly connected
//! components of what calls what, each after those it calls (Kosaraju's).

use std::collections::{HashMap, HashSet};

use super::UnsignedMethod;
use crate::declarations as n;
use crate::hir as h;
use crate::{Symbol, Symbols};

fn graph_visit(node: usize, edges: &[Vec<usize>], seen: &mut [bool], order: &mut Vec<usize>) {
    if std::mem::replace(&mut seen[node], true) {
        return;
    }
    for &next in &edges[node] {
        graph_visit(next, edges, seen, order);
    }
    order.push(node);
}

fn graph_gather(node: usize, edges: &[Vec<usize>], seen: &mut [bool], output: &mut Vec<usize>) {
    if std::mem::replace(&mut seen[node], true) {
        return;
    }
    output.push(node);
    for &next in &edges[node] {
        graph_gather(next, edges, seen, output);
    }
}

pub(super) fn components(
    definitions: &HashMap<Symbol, &n::Function>,
    unsigned: &HashSet<Symbol>,
    methods: &HashMap<Symbol, Vec<UnsignedMethod>>,
    symbols: &Symbols,
) -> Vec<Vec<Symbol>> {
    let names: Vec<_> = unsigned.iter().copied().collect();
    let index: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(index, name)| (*name, index))
        .collect();
    let mut edges = vec![Vec::new(); names.len()];
    for (name, &from) in &index {
        let mut dependencies = HashSet::new();
        for clause in &definitions[name].clauses {
            clause_globals(clause, symbols, &mut dependencies);
        }
        // A member spelled as an unsigned method may be it, which is
        // settled before whatever calls it.
        let spelled: Vec<Symbol> = dependencies
            .iter()
            .filter_map(|dependency| methods.get(dependency))
            .flatten()
            .map(|method| method.name)
            .collect();
        edges[from].extend(
            dependencies
                .into_iter()
                .chain(spelled)
                .filter_map(|dependency| index.get(&dependency).copied()),
        );
    }
    let mut reverse = vec![Vec::new(); names.len()];
    for (from, targets) in edges.iter().enumerate() {
        for target in targets {
            reverse[*target].push(from);
        }
    }
    let mut order = Vec::new();
    let mut seen = vec![false; names.len()];
    for node in 0..names.len() {
        graph_visit(node, &edges, &mut seen, &mut order);
    }
    seen.fill(false);
    let mut result = Vec::new();
    while let Some(node) = order.pop() {
        if seen[node] {
            continue;
        }
        let mut component = Vec::new();
        graph_gather(node, &reverse, &mut seen, &mut component);
        result.push(component.into_iter().map(|index| names[index]).collect());
    }
    result.reverse();
    result
}

/// The member an operator is spelled as, called on its left operand.
pub(super) const fn binary_member(operator: crate::ast::BinaryOp) -> &'static str {
    match operator {
        crate::ast::BinaryOp::Or => "or",
        crate::ast::BinaryOp::Xor => "xor",
        crate::ast::BinaryOp::And => "and",
        crate::ast::BinaryOp::Equal | crate::ast::BinaryOp::NotEqual => "equals",
        crate::ast::BinaryOp::Less
        | crate::ast::BinaryOp::LessEqual
        | crate::ast::BinaryOp::Greater
        | crate::ast::BinaryOp::GreaterEqual => "cmp",
        crate::ast::BinaryOp::Add => "add",
        crate::ast::BinaryOp::Subtract => "sub",
        crate::ast::BinaryOp::Multiply => "mul",
        crate::ast::BinaryOp::Divide => "div",
        crate::ast::BinaryOp::Remainder => "mod",
    }
}

pub(super) const fn unary_member(operator: crate::ast::UnaryOp) -> &'static str {
    match operator {
        crate::ast::UnaryOp::Negate => "neg",
        crate::ast::UnaryOp::Not => "not",
    }
}

fn clause_globals(clause: &h::Clause, symbols: &Symbols, output: &mut HashSet<Symbol>) {
    if let Some(guard) = &clause.guard {
        expr_globals(guard, symbols, output);
    }
    for binding in &clause.body.bindings {
        expr_globals(&binding.value, symbols, output);
    }
    expr_globals(&clause.body.result, symbols, output);
}

fn expr_globals(expression: &h::Expr, symbols: &Symbols, output: &mut HashSet<Symbol>) {
    match &expression.kind {
        h::ExprKind::Global(global) => {
            output.insert(*global);
        }
        // An operator is its member's spelling, as a dot call is.
        h::ExprKind::Unary(operator, _) => output.extend(symbols.find(unary_member(*operator))),
        h::ExprKind::Binary(operator, ..) => {
            output.extend(symbols.find(binary_member(*operator)));
        }
        // A member's spelling too, which names every method spelled so
        // that a definition without a signature may be.
        h::ExprKind::Method(_, member, _, _) | h::ExprKind::Member(_, member) => {
            output.insert(*member);
        }
        _ => {}
    }
    expression.for_each_child(|inner| expr_globals(inner, symbols, output));
}
