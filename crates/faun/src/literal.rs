//! Lossless literal decoding and validation.
//!
//! Parsing stores source spans, not allocated decoded values. Consumers decode
//! only literals they reach; this module is the single authority on escapes,
//! character scalars, and arbitrary-size integer magnitudes.

use std::borrow::Cow;
use std::fmt;

use num_bigint::BigUint;

use super::ast::{Numeral, NumeralKind, Span};
use super::lex::{Kind, Token};

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
            '0' => out.push('\0'),
            'u' => out.push(unicode(&mut chars)?),
            other => {
                return Err(format!(
                    "unknown escape `\\{other}`; use `\\n`, `\\r`, `\\t`, `\\0`, `\\\\`, `\\\"`, `\\'`, `\\$`, or `\\u{{...}}`"
                ));
            }
        }
    }
    Ok(Cow::Owned(out))
}

/// The scalar a `\u{...}` escape names, read from just after the `u`: one
/// to six hexadecimal digits in braces, as Rust writes one.
fn unicode(chars: &mut std::str::Chars<'_>) -> Result<char, String> {
    let malformed =
        || "a `\\u` escape is one to six hexadecimal digits in braces, as `\\u{e9}`".to_owned();
    if chars.next() != Some('{') {
        return Err(malformed());
    }
    let mut value: u32 = 0;
    let mut digits = 0;
    loop {
        match chars.next() {
            Some('}') if digits > 0 => break,
            Some(digit) if digits < 6 => {
                let digit = digit.to_digit(16).ok_or_else(malformed)?;
                value = value * 16 + digit;
                digits += 1;
            }
            _ => return Err(malformed()),
        }
    }
    char::from_u32(value).ok_or_else(|| format!("`\\u{{{value:x}}}` is not a Unicode scalar value"))
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
        NumeralKind::Decimal => Err(LiteralError {
            span: numeral.span,
            message: format!("`{text}` is a decimal, which only a float is"),
        }),
        NumeralKind::Number => {
            BigUint::parse_bytes(numeral.digits(source).as_bytes(), numeral.radix(source))
                .ok_or_else(|| LiteralError {
                    span: numeral.span,
                    message: format!("invalid base-{} numeral `{text}`", numeral.radix(source)),
                })
        }
        NumeralKind::Character => {
            character(numeral.span, text).map(|value| BigUint::from(u32::from(value)))
        }
    }
}

/// Decode a character literal to the scalar it holds.
///
/// # Errors
///
/// Rejects a malformed literal, as [`magnitude`] does.
pub fn scalar(numeral: Numeral, source: &str) -> Result<char, LiteralError> {
    character(numeral.span, numeral.text(source))
}

/// The scalar value a character literal, `text`, holds.
fn character(span: Span, text: &str) -> Result<char, LiteralError> {
    let refused = |message: &str| LiteralError {
        span,
        message: message.to_owned(),
    };
    let inner = text
        .strip_prefix('\'')
        .and_then(|text| text.strip_suffix('\''))
        .ok_or_else(|| refused("invalid character literal"))?;
    let decoded = decode_text(inner).map_err(|message| LiteralError { span, message })?;
    let mut characters = decoded.chars();
    let character = characters
        .next()
        .ok_or_else(|| refused("an empty character literal has no value"))?;
    if characters.next().is_some() {
        return Err(refused("a character literal contains more than one scalar"));
    }
    Ok(character)
}

/// Validate literal tokens in source order, including package paths and
/// literals nested in patterns or interpolations. Integers need no decoding:
/// their digits have already been checked by the lexer.
pub(crate) fn validate(tokens: &[Token], source: &str) -> Result<(), LiteralError> {
    for token in tokens {
        let span = token.span();
        match token.kind {
            Kind::Char => {
                character(span, token.text(source))?;
            }
            Kind::Decimal => {
                decimal(
                    Numeral {
                        span,
                        kind: NumeralKind::Decimal,
                    },
                    source,
                )?;
            }
            Kind::StrText => {
                decode_text(token.text(source))
                    .map_err(|message| LiteralError { span, message })?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// The furthest a decimal's exponent may reach, either way: well past
/// where every float is zero or infinite, and short of numbers too long to
/// hold.
const EXPONENT_LIMIT: u32 = 10_000;

/// A decimal numeral as `digits / 10^scale`: `1.25` is `125` over `10^2`,
/// and `2.5e3` is `2500` over `10^0`.
///
/// # Errors
///
/// Refuses an exponent beyond ten thousand either way.
pub fn decimal(numeral: Numeral, source: &str) -> Result<(BigUint, u32), LiteralError> {
    let text = numeral.text(source);
    let refused = |message: String| LiteralError {
        span: numeral.span,
        message,
    };
    let (significand, exponent) = text
        .split_once(['e', 'E'])
        .map_or((text, "0"), |(significand, exponent)| {
            (significand, exponent)
        });
    let (whole, fraction) = significand.split_once('.').unwrap_or((significand, ""));
    let digits: String = whole.chars().chain(fraction.chars()).collect();
    let digits = BigUint::parse_bytes(digits.as_bytes(), 10)
        .ok_or_else(|| refused(format!("invalid decimal numeral `{text}`")))?;
    let (negative, magnitude) = exponent.strip_prefix('-').map_or_else(
        || (false, exponent.trim_start_matches('+')),
        |rest| (true, rest),
    );
    let magnitude: u32 = magnitude
        .parse()
        .ok()
        .filter(|magnitude| *magnitude <= EXPONENT_LIMIT)
        .ok_or_else(|| {
            refused(format!(
                "the exponent of `{text}` reaches past {EXPONENT_LIMIT}, where every float is nought or infinite"
            ))
        })?;
    let places = u32::try_from(fraction.len()).map_err(|_| refused("too many digits".into()))?;
    if negative {
        return Ok((digits, places + magnitude));
    }
    if magnitude >= places {
        return Ok((digits * BigUint::from(10u8).pow(magnitude - places), 0));
    }
    Ok((digits, places - magnitude))
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

    /// A nought byte, and any scalar by its number, as Rust writes them.
    #[test]
    fn nought_and_any_scalar_have_escapes() {
        assert_eq!(decode_text("a\\0b").unwrap(), "a\0b");
        assert_eq!(decode_text("\\u{e9}\\u{1F600}").unwrap(), "\u{e9}\u{1F600}");
        for malformed in ["\\u", "\\u{}", "\\u{1234567}", "\\u{zz}", "\\ue9", "\\u{e9"] {
            assert!(
                decode_text(malformed).unwrap_err().contains("hexadecimal"),
                "{malformed}"
            );
        }
        assert!(
            decode_text("\\u{D800}")
                .unwrap_err()
                .contains("not a Unicode scalar")
        );
        assert!(
            decode_text("\\u{110000}")
                .unwrap_err()
                .contains("not a Unicode scalar")
        );
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
