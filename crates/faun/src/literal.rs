//! Lossless literal decoding and validation.
//!
//! Parsing stores source spans, not allocated decoded values. Consumers decode
//! only literals they reach; this module is the single authority on escapes,
//! character scalars, and arbitrary-size integer magnitudes.

use std::borrow::Cow;
use std::fmt;

use num_bigint::BigUint;

use super::ast::{
    Body, Clause, Expr, ExprKind, Item, MethodItem, Module, Numeral, NumeralKind, Pattern, Span,
    StringPart,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralError {
    pub span: Span,
    pub message: String,
}

impl fmt::Display for LiteralError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LiteralError {}

/// Decode raw string text, allocating only when it contains an escape.
///
/// # Errors
///
/// Rejects an unknown or trailing escape.
pub fn decode_text(text: &str) -> Result<Cow<'_, str>, String> {
    if !text.as_bytes().contains(&b'\\') {
        return Ok(Cow::Borrowed(text));
    }
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(character) = chars.next() {
        if character != '\\' {
            out.push(character);
            continue;
        }
        let Some(escaped) = chars.next() else {
            return Err("a string cannot end with a backslash".to_string());
        };
        match escaped {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            '$' => out.push('$'),
            other => {
                return Err(format!(
                    "unknown escape `\\{other}`; use `\\n`, `\\r`, `\\t`, `\\\\`, `\\\"`, `\\'`, or `\\$`"
                ));
            }
        }
    }
    Ok(Cow::Owned(out))
}

/// Decode a numeral or character literal to its nonnegative magnitude.
///
/// # Errors
///
/// Rejects a malformed source range. The lexer normally establishes this
/// invariant, but the operation remains total for hand-built syntax.
pub fn magnitude(numeral: Numeral, source: &str) -> Result<BigUint, LiteralError> {
    let text = numeral.text(source);
    match numeral.kind {
        NumeralKind::Number => {
            BigUint::parse_bytes(numeral.digits(source).as_bytes(), numeral.radix(source))
                .ok_or_else(|| LiteralError {
                    span: numeral.span,
                    message: format!("invalid base-{} numeral `{text}`", numeral.radix(source)),
                })
        }
        NumeralKind::Character => {
            let Some(inner) = text
                .strip_prefix('\'')
                .and_then(|text| text.strip_suffix('\''))
            else {
                return Err(LiteralError {
                    span: numeral.span,
                    message: "invalid character literal".to_string(),
                });
            };
            let decoded = decode_text(inner).map_err(|message| LiteralError {
                span: numeral.span,
                message,
            })?;
            let mut characters = decoded.chars();
            let Some(character) = characters.next() else {
                return Err(LiteralError {
                    span: numeral.span,
                    message: "an empty character literal has no value".to_string(),
                });
            };
            if characters.next().is_some() {
                return Err(LiteralError {
                    span: numeral.span,
                    message: "a character literal contains more than one scalar".to_string(),
                });
            }
            Ok(BigUint::from(u32::from(character)))
        }
    }
}

pub(crate) fn validate(module: &Module, source: &str) -> Result<(), LiteralError> {
    for item in &module.items {
        match item {
            Item::Data(data) => {
                for method in &data.methods {
                    match method {
                        MethodItem::Signature(_) => {}
                        MethodItem::Clause(clause) => validate_clause(clause, source)?,
                    }
                }
            }
            Item::Clause(clause) | Item::Expect(clause) => validate_clause(clause, source)?,
            Item::Header(_)
            | Item::Import(_)
            | Item::Exports(_)
            | Item::Alias(_)
            | Item::Constraints(_)
            | Item::Signature(_) => {}
        }
    }
    Ok(())
}

fn validate_clause(clause: &Clause, source: &str) -> Result<(), LiteralError> {
    for pattern in &clause.patterns {
        validate_pattern(pattern, source)?;
    }
    if let Some(guard) = &clause.guard {
        validate_expr(guard, source)?;
    }
    validate_body(&clause.body, source)
}

fn validate_body(body: &Body, source: &str) -> Result<(), LiteralError> {
    for binding in &body.bindings {
        validate_pattern(&binding.pattern, source)?;
        validate_expr(&binding.value, source)?;
    }
    validate_expr(&body.result, source)
}

fn validate_pattern(pattern: &Pattern, source: &str) -> Result<(), LiteralError> {
    match pattern {
        Pattern::Wild(_) | Pattern::Bind(_) => Ok(()),
        Pattern::Constructor { fields, .. } => fields
            .iter()
            .try_for_each(|field| validate_pattern(field, source)),
        Pattern::Number { numeral, .. } => validate_numeral(*numeral, source),
        Pattern::Range { start, end, .. } => {
            validate_numeral(*start, source)?;
            validate_numeral(*end, source)
        }
        Pattern::List { elements, rest, .. } => {
            elements
                .iter()
                .try_for_each(|element| validate_pattern(element, source))?;
            rest.as_deref()
                .map_or(Ok(()), |rest| validate_pattern(rest, source))
        }
        Pattern::Record { fields, .. } => fields
            .iter()
            .try_for_each(|(_, pattern)| validate_pattern(pattern, source)),
        Pattern::Tuple { members, .. }
        | Pattern::Or {
            alternatives: members,
            ..
        } => members
            .iter()
            .try_for_each(|member| validate_pattern(member, source)),
        Pattern::String { parts, .. } => parts.iter().try_for_each(|span| {
            decode_text(span.text(source))
                .map(|_| ())
                .map_err(|message| LiteralError {
                    span: *span,
                    message,
                })
        }),
    }
}

#[allow(clippy::too_many_lines)]
fn validate_expr(expression: &Expr, source: &str) -> Result<(), LiteralError> {
    match &expression.kind {
        ExprKind::Name(_) => Ok(()),
        ExprKind::Number(numeral) => validate_numeral(*numeral, source),
        ExprKind::String(parts) => parts.iter().try_for_each(|part| match part {
            StringPart::Text(span) => {
                decode_text(span.text(source))
                    .map(|_| ())
                    .map_err(|message| LiteralError {
                        span: *span,
                        message,
                    })
            }
            StringPart::Splice(expression) => validate_expr(expression, source),
        }),
        ExprKind::List(elements, rest) => {
            elements
                .iter()
                .try_for_each(|element| validate_expr(element, source))?;
            rest.as_deref()
                .map_or(Ok(()), |rest| validate_expr(rest, source))
        }
        ExprKind::Record(fields) => fields
            .iter()
            .try_for_each(|(_, value)| validate_expr(value, source)),
        ExprKind::Try(value) => validate_expr(value, source),
        ExprKind::Tuple(members) => members
            .iter()
            .try_for_each(|member| validate_expr(member, source)),
        ExprKind::Update(fields, base) => {
            validate_expr(base, source)?;
            fields
                .iter()
                .try_for_each(|(_, value)| validate_expr(value, source))
        }
        ExprKind::Lambda(patterns, body) => {
            patterns
                .iter()
                .try_for_each(|pattern| validate_pattern(pattern, source))?;
            validate_expr(body, source)
        }
        ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
            validate_expr(head, source)?;
            arguments
                .iter()
                .try_for_each(|argument| validate_expr(argument, source))
        }
        ExprKind::Member(head, _) | ExprKind::Unary(_, head) => validate_expr(head, source),
        ExprKind::Binary(_, left, right) => {
            validate_expr(left, source)?;
            validate_expr(right, source)
        }
    }
}

fn validate_numeral(numeral: Numeral, source: &str) -> Result<(), LiteralError> {
    if numeral.kind == NumeralKind::Character {
        magnitude(numeral, source).map(|_| ())
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Numeral, NumeralKind, Span};

    #[test]
    fn decoding_borrows_plain_text_and_allocates_escapes() {
        assert!(matches!(
            decode_text("plain").unwrap(),
            Cow::Borrowed("plain")
        ));
        assert_eq!(decode_text("a\\nb").unwrap(), "a\nb");
        assert!(decode_text("\\q").unwrap_err().contains("unknown escape"));
    }

    #[test]
    fn numerals_are_not_narrowed_to_a_host_word() {
        let source = "340282366920938463463374607431768211456";
        let numeral = Numeral {
            span: Span::new(0, source.len()),
            kind: NumeralKind::Number,
        };
        assert_eq!(magnitude(numeral, source).unwrap().bits(), 129);
    }
}
