//! The lexer: source text to tokens.
//!
//! Ori's syntax separates by juxtaposition and binds by adjacency — `f(x)` is
//! a call and `f (x)` two things, ` -x` negates where `a - b` subtracts — so
//! every token carries whether space, and whether a newline, came before it.
//! That is the whole of what the grammar asks about layout; the grammar itself
//! never sees a space. Comments run from `#` to the end of the line and are
//! space. A string is a run of pieces: text, and `${…}` splices whose contents
//! are ordinary tokens, so the lexer keeps a stack of where it is.
//!
//! A line of items or of a body ends with a [`Kind::Newline`]: where a line
//! break comes after a token a line can end with, and before one a line can
//! begin with, outside every bracket but a method block's. So a line runs on
//! after `->`, `=` or an operator, and into a next line beginning `.`, an
//! infix operator, `where` or `if`, and a list or a call spans lines freely.
//!
//! An operator is read by its spacing, one rule for all of them: after an
//! operand, space on both sides or neither makes it infix, `a - b` or `a-b`,
//! and space before it only makes it a prefix, beginning an element of its
//! own, `[a *rest]`. Where no operand comes before it, it is a prefix however
//! it is spaced. So `-` is [`Kind::Negate`] or [`Kind::Minus`], `*` a
//! [`Kind::Rest`] (also alone before a closing bracket, `[_ *]`) or
//! [`Kind::Star`], and `|` a [`Kind::LambdaBar`] or [`Kind::Bar`]. An infix
//! operator spaced on one side only is [`Kind::Lopsided`], and a `-` beginning
//! an element after another, `[a -b]`, is [`Kind::NegatedElement`] unless it
//! negates a numeral, `[-4 -5]`: both are errors the parser reports.
//!
//! What joins by adjacency is read here too, so the grammar reads kinds
//! alone: a `(` against an operand is a call's, [`Kind::CallParen`]; `.`, `..`,
//! `.*` and `?` go against what they join, or they are [`Kind::Detached`]; and
//! an operand straight against another is [`Kind::Adjacent`], since elements
//! side by side are parted by space.

// Token recognition is clearer as one exhaustive byte match than as forwarding
// helpers cut to satisfy a line-count heuristic.
#![allow(clippy::too_many_lines)]

use super::ast::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A lowercase or `_`-led word: a term, a type variable, a field.
    Ident,
    /// A term name with its `!`: an effectful definition.
    EffectIdent,
    /// A capitalised word: a type or a constructor.
    TypeIdent,
    /// The wildcard `_` alone.
    Wild,
    /// `12`, `0xff`, `0b101`.
    Number,
    /// `1.5`, `2.0e3`: digits either side of a point.
    Decimal,
    /// `'c'`.
    Char,
    /// The opening quote of a string.
    StrStart,
    /// A run of text inside a string, escapes still written.
    StrText,
    /// `${` inside a string; ordinary tokens follow up to the matching `}`.
    SpliceStart,
    /// The `}` that closes a splice.
    SpliceEnd,
    /// The closing quote of a string.
    StrEnd,
    LParen,
    /// `(` straight after an operand: a call's arguments, or a type's.
    CallParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    /// `.(`, opening a method block.
    DotParen,
    /// `.*`, every constructor of a type.
    DotStar,
    /// `..`, a range.
    DotDot,
    Dot,
    Colon,
    Arrow,
    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    /// `-` between two operands.
    Minus,
    /// `-` beginning an operand: a negation.
    Negate,
    /// `*` between two operands.
    Star,
    /// `*` beginning the rest of a list or a record, or standing alone for
    /// one unnamed.
    Rest,
    Slash,
    Percent,
    Amp,
    /// `|` between two operands, or closing a lambda's parameters.
    Bar,
    /// `|` opening a lambda's parameters.
    LambdaBar,
    Caret,
    Bang,
    Question,
    KwIf,
    KwPackage,
    KwImport,
    KwExports,
    KwWhere,
    KwExpect,
    /// A character no token starts with, or a literal left unfinished. The
    /// parser reports it where it meets it.
    Error,
    /// An infix operator with space on one side only, `a- b`: an error.
    Lopsided,
    /// A `-` beginning an element straight after another, `[a -b]`, where it
    /// negates no numeral: an error, being so near `a - b`.
    NegatedElement,
    /// `.`, `..`, `.*` or `?` with space where it joins: an error.
    Detached,
    /// An operand straight after another, `a"b"`: an error, as elements
    /// side by side are parted by space.
    Adjacent,
    /// The end of a line of items or of a body; see the module notes.
    Newline,
    /// The end of the text: every token stream ends with one.
    Eof,
}

impl Kind {
    /// Whether a line can end with this token: it ends a name, a literal, a
    /// bracket, or a `?`.
    const fn ends_line(self) -> bool {
        matches!(
            self,
            Self::Ident
                | Self::EffectIdent
                | Self::TypeIdent
                | Self::Wild
                | Self::Number
                | Self::Decimal
                | Self::Char
                | Self::StrEnd
                | Self::RParen
                | Self::RBracket
                | Self::RBrace
                | Self::DotStar
                | Self::Question
                | Self::Error
        )
    }

    /// Whether an operand can begin with this token.
    const fn begins_operand(self) -> bool {
        matches!(
            self,
            Self::Ident
                | Self::EffectIdent
                | Self::TypeIdent
                | Self::Wild
                | Self::Number
                | Self::Decimal
                | Self::Char
                | Self::StrStart
                | Self::LParen
                | Self::LBracket
                | Self::LBrace
                | Self::Negate
                | Self::Bang
                | Self::LambdaBar
                | Self::Rest
        )
    }

    /// Whether this token only ever stands between two operands.
    const fn infix(self) -> bool {
        matches!(
            self,
            Self::Plus
                | Self::Minus
                | Self::Star
                | Self::Slash
                | Self::Percent
                | Self::Amp
                | Self::Caret
                | Self::EqEq
                | Self::Ne
                | Self::Lt
                | Self::Le
                | Self::Gt
                | Self::Ge
        )
    }

    /// Whether a line beginning with this token goes on with the line
    /// before, as nothing a line holds begins with it. A `-` goes on only
    /// where space follows it; held to what follows, it negates.
    const fn continues_line(self) -> bool {
        matches!(
            self,
            Self::Dot
                | Self::DotParen
                | Self::DotStar
                | Self::DotDot
                | Self::Question
                | Self::Colon
                | Self::Arrow
                | Self::Eq
                | Self::EqEq
                | Self::Ne
                | Self::Lt
                | Self::Le
                | Self::Gt
                | Self::Ge
                | Self::Plus
                | Self::Star
                | Self::Slash
                | Self::Percent
                | Self::Amp
                | Self::Bar
                | Self::Caret
                | Self::KwWhere
                | Self::KwIf
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: Kind,
    pub start: u32,
    pub end: u32,
    /// Whether any space or comment separated this token from the one before.
    pub space_before: bool,
    /// Whether that space held a line break.
    pub newline_before: bool,
}

impl Token {
    /// Return this token's byte range.
    ///
    /// # Panics
    ///
    /// Panics only on a target whose address space cannot represent a `u32`.
    #[must_use]
    pub fn span(self) -> Span {
        let start = usize::try_from(self.start).expect("u32 fits usize");
        let end = usize::try_from(self.end).expect("u32 fits usize");
        Span::new(start, end)
    }

    #[must_use]
    pub fn text(self, src: &str) -> &str {
        self.span().text(src)
    }
}

/// Where the lexer is: in ordinary text, or inside a splice `${…}` of a
/// string, counting the braces opened since, so the one that closes the
/// splice is told from a record's.
enum Mode {
    Splice { depth: u32 },
}

/// A bracket the lexer is inside: lines end within a method block, which
/// holds items, and not within any other.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bracket {
    Lines,
    Joined,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceTooLarge;

impl std::fmt::Display for SourceTooLarge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("source files must be smaller than 4 GiB")
    }
}

impl std::error::Error for SourceTooLarge {}

/// Split source text into compact tokens, retaining only source ranges and layout.
///
/// # Errors
///
/// Refuses a source whose byte offsets cannot fit in a token. Invalid source
/// characters are represented by [`Kind::Error`] for the parser to diagnose.
pub fn lex(src: &str) -> Result<Vec<Token>, SourceTooLarge> {
    if u32::try_from(src.len()).is_err() {
        return Err(SourceTooLarge);
    }
    Ok(Lexer {
        src,
        bytes: src.as_bytes(),
        at: 0,
        out: Vec::with_capacity(src.len() / 4),
        modes: Vec::new(),
        brackets: Vec::new(),
        space_before: false,
        newline_before: false,
    }
    .run())
}

struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    at: usize,
    out: Vec<Token>,
    modes: Vec<Mode>,
    brackets: Vec<Bracket>,
    space_before: bool,
    newline_before: bool,
}

impl Lexer<'_> {
    fn run(mut self) -> Vec<Token> {
        loop {
            self.skip_space();
            let start = self.at;
            let Some(&byte) = self.bytes.get(self.at) else {
                self.push(Kind::Eof, start);
                return self.out;
            };
            let kind = match byte {
                b'"' => {
                    self.at += 1;
                    self.push(Kind::StrStart, start);
                    self.string();
                    continue;
                }
                b'\'' => self.char_literal(),
                b'0'..=b'9' => self.number(),
                b'a'..=b'z' | b'_' => self.word(),
                b'A'..=b'Z' => {
                    self.at += 1;
                    self.eat_word_chars();
                    Kind::TypeIdent
                }
                b'}' => {
                    self.at += 1;
                    match self.modes.last_mut() {
                        Some(Mode::Splice { depth }) if *depth == 0 => {
                            self.modes.pop();
                            self.push(Kind::SpliceEnd, start);
                            self.string();
                            continue;
                        }
                        Some(Mode::Splice { depth }) => {
                            *depth -= 1;
                            Kind::RBrace
                        }
                        None => Kind::RBrace,
                    }
                }
                b'{' => {
                    self.at += 1;
                    if let Some(Mode::Splice { depth }) = self.modes.last_mut() {
                        *depth += 1;
                    }
                    Kind::LBrace
                }
                _ => self.punctuation(),
            };
            self.push(kind, start);
        }
    }

    fn push(&mut self, kind: Kind, start: usize) {
        if self.newline_before && self.ends_line_before(kind) {
            let at = self.out.last().expect("a token before a line break").end;
            self.out.push(Token {
                kind: Kind::Newline,
                start: at,
                end: at,
                space_before: false,
                newline_before: false,
            });
        }
        let kind = self.classify(kind);
        match kind {
            Kind::DotParen => self.brackets.push(Bracket::Lines),
            Kind::LParen | Kind::CallParen | Kind::LBracket | Kind::LBrace => {
                self.brackets.push(Bracket::Joined);
            }
            Kind::RParen | Kind::RBracket | Kind::RBrace => {
                self.brackets.pop();
            }
            _ => {}
        }
        self.out.push(Token {
            kind,
            start: u32::try_from(start).expect("source length checked before lexing"),
            end: u32::try_from(self.at).expect("source length checked before lexing"),
            space_before: self.space_before,
            newline_before: self.newline_before,
        });
        self.space_before = false;
        self.newline_before = false;
    }

    /// An operator just lexed, read by its spacing and by whether an operand
    /// comes before it; see the module notes.
    fn classify(&self, kind: Kind) -> Kind {
        let operand = self.out.last().is_some_and(|last| last.kind.ends_line());
        let (before, after) = (self.space_before, self.space_after());
        let prefix = !operand || before && !after;
        let kind = match kind {
            Kind::Minus if !operand => Kind::Negate,
            Kind::Minus if prefix && self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) => {
                Kind::Negate
            }
            Kind::Minus if prefix => Kind::NegatedElement,
            Kind::Star if prefix || before && self.closes_next() => Kind::Rest,
            Kind::Bar if prefix => Kind::LambdaBar,
            kind if kind.infix() && before != after => Kind::Lopsided,
            Kind::LParen if operand && !before => Kind::CallParen,
            Kind::Dot if before && !self.newline_before || after => Kind::Detached,
            Kind::DotDot if before || after => Kind::Detached,
            Kind::DotStar | Kind::Question if before => Kind::Detached,
            kind => kind,
        };
        if operand && !before && kind.begins_operand() {
            Kind::Adjacent
        } else {
            kind
        }
    }

    /// Whether space, a comment or the end of the text follows what was just
    /// lexed.
    fn space_after(&self) -> bool {
        self.bytes
            .get(self.at)
            .is_none_or(|byte| matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | b'#'))
    }

    /// Whether the next token, past any space, closes a list or a record.
    fn closes_next(&self) -> bool {
        self.bytes[self.at..]
            .iter()
            .find(|byte| !matches!(byte, b' ' | b'\t' | b'\n' | b'\r'))
            .is_some_and(|byte| matches!(byte, b']' | b'}'))
    }

    /// Whether the line break before `kind`, just lexed, ends a line.
    fn ends_line_before(&self, kind: Kind) -> bool {
        let lines = self.modes.is_empty()
            && self
                .brackets
                .last()
                .is_none_or(|bracket| *bracket == Bracket::Lines);
        let held_minus = kind == Kind::Minus && !self.space_after();
        lines
            && kind != Kind::Eof
            && self.out.last().is_some_and(|last| last.kind.ends_line())
            && (!kind.continues_line() && (kind != Kind::Minus || held_minus))
    }

    fn skip_space(&mut self) {
        while let Some(&byte) = self.bytes.get(self.at) {
            match byte {
                b' ' | b'\t' => self.at += 1,
                b'\n' | b'\r' => {
                    self.newline_before = true;
                    self.at += 1;
                }
                b'#' => {
                    while let Some(&byte) = self.bytes.get(self.at)
                        && byte != b'\n'
                        && byte != b'\r'
                    {
                        self.at += 1;
                    }
                }
                _ => return,
            }
            self.space_before = true;
        }
    }

    /// The pieces of a string after its opening quote or a splice's end, up
    /// to and including the closing quote or the next splice's start.
    fn string(&mut self) {
        let start = self.at;
        while let Some(&byte) = self.bytes.get(self.at) {
            match byte {
                b'"' => break,
                b'$' if self.bytes.get(self.at + 1) == Some(&b'{') => break,
                b'\\' => {
                    self.at += 1;
                    if let Some(c) = self.src[self.at..].chars().next() {
                        self.at += c.len_utf8();
                    }
                }
                _ => self.at += 1,
            }
        }
        if self.at > start {
            self.push(Kind::StrText, start);
        }
        let start = self.at;
        match self.bytes.get(self.at) {
            Some(b'"') => {
                self.at += 1;
                self.push(Kind::StrEnd, start);
            }
            Some(b'$') => {
                self.at += 2;
                self.push(Kind::SpliceStart, start);
                self.modes.push(Mode::Splice { depth: 0 });
            }
            _ => {
                // Unterminated: what is left is an error token, and the
                // parser says where the string began.
                self.push(Kind::Error, start);
            }
        }
    }

    fn char_literal(&mut self) -> Kind {
        let start = self.at;
        self.at += 1;
        match self.bytes.get(self.at) {
            Some(b'\\') => {
                self.at += 1;
                match self.src[self.at..].chars().next() {
                    Some(c) => self.at += c.len_utf8(),
                    None => return Kind::Error,
                }
            }
            Some(b'\'' | b'\n' | b'\r') | None => {
                self.at = start + 1;
                return Kind::Error;
            }
            Some(_) => {
                let c = self.src[self.at..].chars().next().expect("a character");
                self.at += c.len_utf8();
            }
        }
        if self.bytes.get(self.at) == Some(&b'\'') {
            self.at += 1;
            Kind::Char
        } else {
            Kind::Error
        }
    }

    fn number(&mut self) -> Kind {
        let radix = match (self.bytes.get(self.at), self.bytes.get(self.at + 1)) {
            (Some(b'0'), Some(b'x')) => Some(16),
            (Some(b'0'), Some(b'b')) => Some(2),
            _ => None,
        };
        let mut kind = Kind::Number;
        if let Some(radix) = radix {
            self.at += 2;
            let digits = self.at;
            while self
                .bytes
                .get(self.at)
                .is_some_and(|byte| char::from(*byte).is_digit(radix))
            {
                self.at += 1;
            }
            if self.at == digits {
                return Kind::Error;
            }
        } else {
            self.eat_digits();
            // A point with digits after it makes a decimal; `2.pow(k)`
            // and `1..3` keep their points for the grammar.
            if self.bytes.get(self.at) == Some(&b'.')
                && self.bytes.get(self.at + 1).is_some_and(u8::is_ascii_digit)
            {
                self.at += 1;
                self.eat_digits();
                if matches!(self.bytes.get(self.at), Some(b'e' | b'E')) {
                    let mark = self.at;
                    self.at += 1;
                    if matches!(self.bytes.get(self.at), Some(b'+' | b'-')) {
                        self.at += 1;
                    }
                    if self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) {
                        self.eat_digits();
                    } else {
                        self.at = mark;
                    }
                }
                kind = Kind::Decimal;
            }
        }
        // A numeral ends where a word would: `1True` is no token at all.
        if self
            .bytes
            .get(self.at)
            .is_some_and(|byte| is_word_char(*byte))
        {
            self.eat_word_chars();
            return Kind::Error;
        }
        kind
    }

    fn eat_digits(&mut self) {
        while self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) {
            self.at += 1;
        }
    }

    fn eat_word_chars(&mut self) {
        while self
            .bytes
            .get(self.at)
            .is_some_and(|byte| is_word_char(*byte))
        {
            self.at += 1;
        }
    }

    fn word(&mut self) -> Kind {
        let start = self.at;
        self.at += 1;
        self.eat_word_chars();
        let text = &self.src[start..self.at];
        let kind = match text {
            "_" => return Kind::Wild,
            "if" => Kind::KwIf,
            "package" => Kind::KwPackage,
            "import" => Kind::KwImport,
            "exports" => Kind::KwExports,
            "where" => Kind::KwWhere,
            "expect" => Kind::KwExpect,
            _ => Kind::Ident,
        };
        if kind != Kind::Ident {
            return kind;
        }
        // A trailing `!` is the effect colour, unless it begins `!=`.
        if self.bytes.get(self.at) == Some(&b'!') && self.bytes.get(self.at + 1) != Some(&b'=') {
            self.at += 1;
            return Kind::EffectIdent;
        }
        Kind::Ident
    }

    fn punctuation(&mut self) -> Kind {
        let two = |lexer: &mut Self, kind: Kind| {
            lexer.at += 2;
            kind
        };
        let one = |lexer: &mut Self, kind: Kind| {
            lexer.at += 1;
            kind
        };
        let next = self.bytes.get(self.at + 1).copied();
        match self.bytes[self.at] {
            b'-' if next == Some(b'>') => two(self, Kind::Arrow),
            b'-' => one(self, Kind::Minus),
            b'.' if next == Some(b'.') => two(self, Kind::DotDot),
            b'.' if next == Some(b'(') => two(self, Kind::DotParen),
            b'.' if next == Some(b'*') => two(self, Kind::DotStar),
            b'.' => one(self, Kind::Dot),
            b'=' if next == Some(b'=') => two(self, Kind::EqEq),
            b'=' => one(self, Kind::Eq),
            b'!' if next == Some(b'=') => two(self, Kind::Ne),
            b'!' => one(self, Kind::Bang),
            b'<' if next == Some(b'=') => two(self, Kind::Le),
            b'<' => one(self, Kind::Lt),
            b'>' if next == Some(b'=') => two(self, Kind::Ge),
            b'>' => one(self, Kind::Gt),
            b'+' => one(self, Kind::Plus),
            b'*' => one(self, Kind::Star),
            b'/' => one(self, Kind::Slash),
            b'%' => one(self, Kind::Percent),
            b'&' => one(self, Kind::Amp),
            b'|' => one(self, Kind::Bar),
            b'^' => one(self, Kind::Caret),
            b'?' => one(self, Kind::Question),
            b':' => one(self, Kind::Colon),
            b'(' => one(self, Kind::LParen),
            b')' => one(self, Kind::RParen),
            b'[' => one(self, Kind::LBracket),
            b']' => one(self, Kind::RBracket),
            _ => {
                let c = self.src[self.at..].chars().next().expect("a character");
                self.at += c.len_utf8();
                Kind::Error
            }
        }
    }
}

const fn is_word_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<Kind> {
        lex(src).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn adjacency_is_recorded_on_the_token() {
        let tokens = lex("f (x)").unwrap();
        assert_eq!(tokens[1].kind, Kind::LParen);
        assert!(tokens[1].space_before);
        let tokens = lex("f(x)").unwrap();
        assert!(!tokens[1].space_before);
        let tokens = lex("x\n  .y").unwrap();
        assert!(tokens[1].newline_before && tokens[1].space_before);
    }

    #[test]
    fn strings_splice_ordinary_tokens() {
        assert_eq!(
            kinds(r#""a${x}b""#),
            [
                Kind::StrStart,
                Kind::StrText,
                Kind::SpliceStart,
                Kind::Ident,
                Kind::SpliceEnd,
                Kind::StrText,
                Kind::StrEnd,
                Kind::Eof
            ]
        );
        assert_eq!(
            kinds(r#""${{x: 1}.x}""#)[..],
            [
                Kind::StrStart,
                Kind::SpliceStart,
                Kind::LBrace,
                Kind::Ident,
                Kind::Colon,
                Kind::Number,
                Kind::RBrace,
                Kind::Dot,
                Kind::Ident,
                Kind::SpliceEnd,
                Kind::StrEnd,
                Kind::Eof
            ]
        );
        assert_eq!(
            kinds(r#""\"\${""#),
            [Kind::StrStart, Kind::StrText, Kind::StrEnd, Kind::Eof]
        );
    }

    #[test]
    fn numerals_keep_their_points_for_the_grammar() {
        assert_eq!(
            kinds("1..3")[..3],
            [Kind::Number, Kind::DotDot, Kind::Number]
        );
        assert_eq!(
            kinds("2.pow(k)")[..3],
            [Kind::Number, Kind::Dot, Kind::Ident]
        );
        assert_eq!(kinds("1.5e3")[0], Kind::Decimal);
        assert_eq!(kinds("0xffTrue")[0], Kind::Error);
        assert_eq!(kinds("0x")[0], Kind::Error);
    }

    #[test]
    fn lines_end_between_what_ends_one_and_what_begins_one() {
        use Kind::{Arrow, Dot, DotParen, Ident, LParen, Minus, Newline, RParen, TypeIdent};
        assert_eq!(kinds("a\nb"), [Ident, Newline, Ident, Kind::Eof]);
        assert_eq!(kinds("a # note\n\n\nb")[..3], [Ident, Newline, Ident]);
        // After what cannot end a line, and before what cannot begin one,
        // the line goes on.
        assert_eq!(kinds("a ->\nb"), [Ident, Arrow, Ident, Kind::Eof]);
        assert_eq!(kinds("a\n  .b"), [Ident, Dot, Ident, Kind::Eof]);
        assert_eq!(kinds("a\n- b"), [Ident, Minus, Ident, Kind::Eof]);
        assert_eq!(
            kinds("a\n-b"),
            [Ident, Newline, Kind::Negate, Ident, Kind::Eof]
        );
        // Brackets join their lines, but a method block holds lines of items.
        assert_eq!(kinds("(a\nb)"), [LParen, Ident, Ident, RParen, Kind::Eof]);
        assert_eq!(
            kinds("T.(a\nb\n)"),
            [
                TypeIdent,
                DotParen,
                Ident,
                Newline,
                Ident,
                Newline,
                RParen,
                Kind::Eof
            ]
        );
        assert_eq!(kinds("\"${a\nb}\"")[2..4], [Ident, Ident]);
        assert_eq!(kinds("a\n"), [Ident, Kind::Eof]);
    }

    #[test]
    fn an_operator_is_read_by_its_spacing() {
        use Kind::{
            Bar, Ident, LBracket, LambdaBar, Lopsided, Minus, Negate, NegatedElement, Number,
            RBrace, RBracket, Rest, Star,
        };
        assert_eq!(kinds("a - b")[1], Minus);
        assert_eq!(kinds("a-b")[1], Minus);
        assert_eq!(kinds("x = - b")[2], Negate);
        assert_eq!(
            kinds("[-4 -5]")[..5],
            [LBracket, Negate, Number, Negate, Number]
        );
        assert_eq!(kinds("[a -b]")[2], NegatedElement);
        assert_eq!(kinds("a- b")[1], Lopsided);
        assert_eq!(kinds("a +b")[1], Lopsided);
        assert_eq!(kinds("a * b")[1], Star);
        assert_eq!(kinds("[a *rest]")[2..4], [Rest, Ident]);
        assert_eq!(kinds("[_ *]")[2..4], [Rest, RBracket]);
        assert_eq!(kinds("{x * }")[2..4], [Rest, RBrace]);
        assert_eq!(kinds("a | b")[1], Bar);
        assert_eq!(kinds("f(a |x| x)")[3..7], [LambdaBar, Ident, Bar, Ident]);
    }

    #[test]
    fn effect_names_keep_their_bang_but_not_a_comparison() {
        assert_eq!(kinds("f!")[0], Kind::EffectIdent);
        assert_eq!(kinds("a!=b")[..3], [Kind::Ident, Kind::Ne, Kind::Ident]);
        assert_eq!(kinds("_")[0], Kind::Wild);
        assert_eq!(kinds("_x")[0], Kind::Ident);
        assert_eq!(kinds("iffy")[0], Kind::Ident);
        assert_eq!(kinds("if")[0], Kind::KwIf);
    }
}
