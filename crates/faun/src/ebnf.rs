//! The grammar written out in `grammar.ebnf`, held to the parser.
//!
//! The file is read here into rules, which must be LL(1): at every choice,
//! the next token names the one way on. A recognizer made from them, which
//! only ever looks at the next token, must then read what the parser reads,
//! from every program in the repository and from programs written to probe
//! each rule, so the file and the parser cannot drift apart unnoticed.

use super::lex::{self, Kind, Token};
use std::collections::HashMap;
use std::path::Path;

const GRAMMAR: &str = include_str!("grammar.ebnf");

/// A set of the grammar's terminals, each by its number.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Kinds(u128);

impl Kinds {
    fn one(terminal: usize) -> Self {
        let at = u32::try_from(terminal).expect("a terminal's number fits");
        Self(
            1_u128
                .checked_shl(at)
                .expect("the grammar has under 128 terminals"),
        )
    }

    const fn with(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn has(self, terminal: Option<usize>) -> bool {
        terminal.is_some_and(|terminal| self.meets(Self::one(terminal)))
    }

    const fn meets(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

#[derive(Debug)]
enum Node {
    Sequence(Vec<Self>),
    Choice(Vec<Self>),
    Optional(Box<Self>),
    Repeated(Box<Self>),
    /// A terminal, by its number in [`Grammar::terminals`].
    Token(usize),
    Rule(usize),
}

struct Grammar {
    names: Vec<String>,
    /// The token kind each terminal is.
    terminals: Vec<Kind>,
    rules: Vec<Node>,
    nullable: Vec<bool>,
    first: Vec<Kinds>,
    follow: Vec<Kinds>,
}

/// The token kind a terminal spells.
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each terminal the grammar spells"
)]
fn terminal(spelling: &str) -> Kind {
    match spelling {
        "NEWLINE" => Kind::Newline,
        "EOF" => Kind::Eof,
        "NAME" => Kind::Ident,
        "EFFECT" => Kind::EffectIdent,
        "TYPE" => Kind::TypeIdent,
        "NUMBER" => Kind::Number,
        "DECIMAL" => Kind::Decimal,
        "CHAR" => Kind::Char,
        "STR_START" => Kind::StrStart,
        "STR_TEXT" => Kind::StrText,
        "STR_END" => Kind::StrEnd,
        "SPLICE_START" => Kind::SpliceStart,
        "SPLICE_END" => Kind::SpliceEnd,
        "CALL_PAREN" => Kind::CallParen,
        "NEGATE" => Kind::Negate,
        "REST" => Kind::Rest,
        "LAMBDA_BAR" => Kind::LambdaBar,
        "\"_\"" => Kind::Wild,
        "\"package\"" => Kind::KwPackage,
        "\"import\"" => Kind::KwImport,
        "\"exports\"" => Kind::KwExports,
        "\"expect\"" => Kind::KwExpect,
        "\"where\"" => Kind::KwWhere,
        "\"if\"" => Kind::KwIf,
        "\"(\"" => Kind::LParen,
        "\")\"" => Kind::RParen,
        "\"[\"" => Kind::LBracket,
        "\"]\"" => Kind::RBracket,
        "\"{\"" => Kind::LBrace,
        "\"}\"" => Kind::RBrace,
        "\".(\"" => Kind::DotParen,
        "\".*\"" => Kind::DotStar,
        "\"..\"" => Kind::DotDot,
        "\".\"" => Kind::Dot,
        "\":\"" => Kind::Colon,
        "\"->\"" => Kind::Arrow,
        "\"=\"" => Kind::Eq,
        "\"?\"" => Kind::Question,
        "\"!\"" => Kind::Bang,
        "\"|\"" => Kind::Bar,
        "\"^\"" => Kind::Caret,
        "\"&\"" => Kind::Amp,
        "\"==\"" => Kind::EqEq,
        "\"!=\"" => Kind::Ne,
        "\"<\"" => Kind::Lt,
        "\"<=\"" => Kind::Le,
        "\">\"" => Kind::Gt,
        "\">=\"" => Kind::Ge,
        "\"+\"" => Kind::Plus,
        "\"-\"" => Kind::Minus,
        "\"/\"" => Kind::Slash,
        "\"%\"" => Kind::Percent,
        "\"*\"" => Kind::Star,
        other => panic!("grammar.ebnf names no token kind `{other}`"),
    }
}

/// The words of the file: names, terminals and punctuation, comments gone.
fn words(text: &str) -> Vec<&str> {
    let mut words = Vec::new();
    let mut rest = text;
    loop {
        rest = rest.trim_start();
        if let Some(after) = rest.strip_prefix("(*") {
            let end = after.find("*)").expect("a comment closes");
            rest = &after[end + 2..];
            continue;
        }
        let Some(first) = rest.chars().next() else {
            return words;
        };
        let length = if first == '"' {
            rest[1..].find('"').expect("a terminal closes") + 2
        } else if first.is_ascii_alphabetic() {
            rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '-'))
                .unwrap_or(rest.len())
        } else {
            1
        };
        words.push(&rest[..length]);
        rest = &rest[length..];
    }
}

impl Grammar {
    fn read(text: &str) -> Self {
        let words = words(text);
        let mut names: Vec<String> = Vec::new();
        for (at, word) in words.iter().enumerate() {
            if words.get(at + 1) == Some(&"=") && word.starts_with(|c: char| c.is_ascii_lowercase())
            {
                names.push((*word).to_owned());
            }
        }
        let index: HashMap<&str, usize> = names
            .iter()
            .enumerate()
            .map(|(at, name)| (name.as_str(), at))
            .collect();
        let mut reader = Reader {
            words: &words,
            at: 0,
            index: &index,
            terminals: Vec::new(),
        };
        let mut rules = Vec::new();
        while reader.at < words.len() {
            reader.next();
            assert_eq!(reader.next(), "=", "a rule is `name = ...`");
            rules.push(reader.choice());
            assert_eq!(reader.next(), ";", "a rule ends with `;`");
        }
        let mut grammar = Self {
            terminals: reader.terminals,
            nullable: vec![false; rules.len()],
            first: vec![Kinds::default(); rules.len()],
            follow: vec![Kinds::default(); rules.len()],
            names,
            rules,
        };
        grammar.solve();
        grammar
    }

    /// Which rules read nothing, what each begins with, and what may
    /// follow each: the least sets that hold, found by repeating until
    /// none grows.
    fn solve(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for rule in 0..self.rules.len() {
                let nullable = self.nullable(&self.rules[rule]);
                let first = self.first(&self.rules[rule]);
                changed |= nullable != self.nullable[rule] || first != self.first[rule];
                self.nullable[rule] = nullable;
                self.first[rule] = first;
            }
        }
        let mut changed = true;
        while changed {
            let before = self.follow.clone();
            for (body, &after) in self.rules.iter().zip(&before) {
                let mut follow = std::mem::take(&mut self.follow);
                self.visit(body, after, &mut |node, after| {
                    if let Node::Rule(inner) = node {
                        follow[*inner] = follow[*inner].with(after);
                    }
                });
                self.follow = follow;
            }
            changed = self.follow != before;
        }
    }

    fn nullable(&self, node: &Node) -> bool {
        match node {
            Node::Sequence(items) => items.iter().all(|item| self.nullable(item)),
            Node::Choice(branches) => branches.iter().any(|branch| self.nullable(branch)),
            Node::Optional(_) | Node::Repeated(_) => true,
            Node::Token(_) => false,
            Node::Rule(rule) => self.nullable[*rule],
        }
    }

    fn first(&self, node: &Node) -> Kinds {
        match node {
            Node::Sequence(items) => {
                let mut first = Kinds::default();
                for item in items {
                    first = first.with(self.first(item));
                    if !self.nullable(item) {
                        break;
                    }
                }
                first
            }
            Node::Choice(branches) => branches.iter().fold(Kinds::default(), |first, branch| {
                first.with(self.first(branch))
            }),
            Node::Optional(inner) | Node::Repeated(inner) => self.first(inner),
            Node::Token(terminal) => Kinds::one(*terminal),
            Node::Rule(rule) => self.first[*rule],
        }
    }

    /// Call `seen` with every node under `node` and what may follow it,
    /// where `after` may follow `node`.
    fn visit(&self, node: &Node, after: Kinds, seen: &mut impl FnMut(&Node, Kinds)) {
        seen(node, after);
        match node {
            Node::Sequence(items) => {
                let mut follow = after;
                for item in items.iter().rev() {
                    self.visit(item, follow, seen);
                    follow = if self.nullable(item) {
                        follow.with(self.first(item))
                    } else {
                        self.first(item)
                    };
                }
            }
            Node::Choice(branches) => {
                for branch in branches {
                    self.visit(branch, after, seen);
                }
            }
            Node::Optional(inner) => self.visit(inner, after, seen),
            Node::Repeated(inner) => self.visit(inner, after.with(self.first(inner)), seen),
            Node::Token(_) | Node::Rule(_) => {}
        }
    }

    /// Every choice the next token does not settle, each said in words.
    fn conflicts(&self) -> Vec<String> {
        let mut conflicts = Vec::new();
        for (rule, body) in self.rules.iter().enumerate() {
            let name = &self.names[rule];
            self.visit(body, self.follow[rule], &mut |node, after| match node {
                Node::Choice(branches) => {
                    let mut seen = Kinds::default();
                    for branch in branches {
                        let first = self.first(branch);
                        if first.meets(seen) {
                            conflicts.push(format!("`{name}`: two branches begin alike"));
                        }
                        seen = seen.with(first);
                    }
                    let empty = branches
                        .iter()
                        .filter(|branch| self.nullable(branch))
                        .count();
                    if empty > 1 {
                        conflicts.push(format!("`{name}`: two branches may be empty"));
                    }
                    if empty > 0 && seen.meets(after) {
                        conflicts.push(format!(
                            "`{name}`: a branch begins as what follows an empty one"
                        ));
                    }
                }
                Node::Optional(inner) | Node::Repeated(inner) => {
                    if self.nullable(inner) {
                        conflicts.push(format!("`{name}`: an optional part may be empty"));
                    }
                    if self.first(inner).meets(after) {
                        conflicts.push(format!(
                            "`{name}`: an optional part begins as what follows it"
                        ));
                    }
                }
                _ => {}
            });
        }
        conflicts
    }

    /// Whether `tokens` are a file, read by the next token alone.
    fn reads(&self, tokens: &[Token]) -> Result<(), usize> {
        let mut at = 0;
        self.read_node(&self.rules[0], tokens, &mut at)?;
        if at == tokens.len() { Ok(()) } else { Err(at) }
    }

    /// The number of the terminal the token at `at` is, if the grammar
    /// has one for it.
    fn terminal_at(&self, tokens: &[Token], at: usize) -> Option<usize> {
        let kind = tokens.get(at).map_or(Kind::Eof, |token| token.kind);
        self.terminals.iter().position(|terminal| *terminal == kind)
    }

    fn read_node(&self, node: &Node, tokens: &[Token], at: &mut usize) -> Result<(), usize> {
        let next = self.terminal_at(tokens, *at);
        match node {
            Node::Sequence(items) => items
                .iter()
                .try_for_each(|item| self.read_node(item, tokens, at)),
            Node::Choice(branches) => {
                let branch = branches
                    .iter()
                    .find(|branch| self.first(branch).has(next))
                    .or_else(|| branches.iter().find(|branch| self.nullable(branch)))
                    .ok_or(*at)?;
                self.read_node(branch, tokens, at)
            }
            Node::Optional(inner) => {
                if self.first(inner).has(next) {
                    self.read_node(inner, tokens, at)?;
                }
                Ok(())
            }
            Node::Repeated(inner) => {
                while self.first(inner).has(self.terminal_at(tokens, *at)) {
                    self.read_node(inner, tokens, at)?;
                }
                Ok(())
            }
            Node::Token(terminal) => {
                if next == Some(*terminal) {
                    *at += 1;
                    Ok(())
                } else {
                    Err(*at)
                }
            }
            Node::Rule(rule) => self.read_node(&self.rules[*rule], tokens, at),
        }
    }

    /// The rules `file` never reaches.
    fn unreached(&self) -> Vec<&str> {
        let mut reached = vec![false; self.rules.len()];
        let mut waiting = vec![0];
        while let Some(rule) = waiting.pop() {
            if std::mem::replace(&mut reached[rule], true) {
                continue;
            }
            self.visit(&self.rules[rule], Kinds::default(), &mut |node, _| {
                if let Node::Rule(inner) = node {
                    waiting.push(*inner);
                }
            });
        }
        self.names
            .iter()
            .zip(reached)
            .filter(|(_, reached)| !reached)
            .map(|(name, _)| name.as_str())
            .collect()
    }
}

struct Reader<'w> {
    words: &'w [&'w str],
    at: usize,
    index: &'w HashMap<&'w str, usize>,
    terminals: Vec<Kind>,
}

impl Reader<'_> {
    fn next(&mut self) -> &str {
        let word = self.words[self.at];
        self.at += 1;
        word
    }

    fn peek(&self) -> Option<&str> {
        self.words.get(self.at).copied()
    }

    fn choice(&mut self) -> Node {
        let mut branches = vec![self.sequence()];
        while self.peek() == Some("|") {
            self.next();
            branches.push(self.sequence());
        }
        if branches.len() == 1 {
            branches.pop().expect("one branch")
        } else {
            Node::Choice(branches)
        }
    }

    fn sequence(&mut self) -> Node {
        let mut items = Vec::new();
        while let Some(word) = self.peek()
            && !matches!(word, "|" | ";" | "]" | "}" | ")")
        {
            items.push(self.item());
        }
        if items.len() == 1 {
            items.pop().expect("one item")
        } else {
            Node::Sequence(items)
        }
    }

    fn item(&mut self) -> Node {
        let word = self.next().to_owned();
        let closed = |reader: &mut Self, close: &str| {
            let inner = reader.choice();
            assert_eq!(reader.next(), close, "a bracket closes");
            inner
        };
        match word.as_str() {
            "[" => Node::Optional(Box::new(closed(self, "]"))),
            "{" => Node::Repeated(Box::new(closed(self, "}"))),
            "(" => closed(self, ")"),
            name if name.starts_with(|c: char| c.is_ascii_lowercase()) => Node::Rule(
                *self
                    .index
                    .get(name)
                    .unwrap_or_else(|| panic!("grammar.ebnf has no rule `{name}`")),
            ),
            spelling => {
                let kind = terminal(spelling);
                let number = self
                    .terminals
                    .iter()
                    .position(|known| *known == kind)
                    .unwrap_or_else(|| {
                        self.terminals.push(kind);
                        self.terminals.len() - 1
                    });
                Node::Token(number)
            }
        }
    }
}

/// Every Faun source in the repository.
fn sources() -> Vec<(String, String)> {
    fn gather(directory: &Path, found: &mut Vec<(String, String)>) {
        for entry in std::fs::read_dir(directory).expect("a directory") {
            let path = entry.expect("an entry").path();
            if path.is_dir() {
                gather(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "fn") {
                let text = std::fs::read_to_string(&path).expect("a source");
                found.push((path.display().to_string(), text));
            }
        }
    }
    let mut found = Vec::new();
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    gather(&crates, &mut found);
    assert!(found.len() > 20, "the repository's programs are found");
    found
}

/// Whether the grammar and the parser both read `source`, or both refuse it.
fn agree(grammar: &Grammar, label: &str, source: &str) -> bool {
    let tokens = lex::lex(source).expect("a small source");
    let grammar_reads = grammar.reads(&tokens);
    let parser_reads = super::grammar::file(&tokens, source).1.is_empty();
    assert_eq!(
        grammar_reads.is_ok(),
        parser_reads,
        "{label}: grammar.ebnf {} it, and the parser {} it (grammar stopped at token {:?})",
        if grammar_reads.is_ok() {
            "reads"
        } else {
            "refuses"
        },
        if parser_reads { "reads" } else { "refuses" },
        grammar_reads.err(),
    );
    parser_reads
}

#[test]
fn the_grammar_is_ll1_and_every_rule_is_used() {
    let grammar = Grammar::read(GRAMMAR);
    assert_eq!(grammar.conflicts(), Vec::<String>::new());
    assert_eq!(grammar.unreached(), Vec::<&str>::new());
}

#[test]
fn the_grammar_reads_every_program_in_the_repository_as_the_parser_does() {
    let grammar = Grammar::read(GRAMMAR);
    for (path, source) in sources() {
        assert!(agree(&grammar, &path, &source), "{path} is read");
    }
}

#[test]
fn the_grammar_reads_and_refuses_what_the_parser_does() {
    let grammar = Grammar::read(GRAMMAR);
    let read = [
        "import std.host {Host List.* x: y}\nexports {f Host.*}\npackage {md5: \"../md5\"}\n",
        "f : List(a) (a -> b) -> {x: a *} where Show(a) Eq(a) a.show : a -> Str\n",
        "sum : List(a) -> a where\n  a.zero : a\n  a.add : a a -> a\n",
        "Maybe(a) : [None Some(a)].(\n  map : Maybe(a) (a -> b) -> Maybe(b)\n  map(None _) -> None\n  map(Some(x) f) -> Some(f(x))\n)\n",
        "Name = (a b -> c)\nNum(a) = where a.add : a a -> a\n",
        "f(x) if x > 0 ->\n  log!(x)\n  [y *rest] = x\n  {a b: c *} = y\n  -a * 2 + c?.d.e(|p Q(r)| p) | !b\n",
        "expect 'a'..'z' == \"s${x}t\"\n",
        "f(x) -> [(x) (x y) _ 1.5 -2 *xs]\nx = 1\nx\n",
        "f(x) -> x\n  .map(g)\n  .filter(h) +\n  1\n",
        "f([x *r] {a *}) if x.p(|y| y) ^ !a ->\n  r\nf(_ _) if\n  (a b) == c -> 0\n",
        "T : [A B].(\n  f(A) if g() -> 1\n  f(_) -> 0\n)\n",
        "",
    ];
    for source in read {
        assert!(agree(&grammar, source, source), "{source} is read");
    }
    let refused = [
        "f : a -> a where a.zero : a b.one : b\n",
        "main! : Host -> [] main!(host) -> 0\n",
        "Name = 1 + 2\n",
        "f(x) -> x .y\n",
        "f(x) -> x?? .y\n",
        "f(x) -> [a\"b\"]\n",
        "f(x) -> a- b\n",
        "f(x) -> [a -b]\n",
        "f(x) -> (x -> x)\n",
        "f(x) -> x ->\n",
        "f(x) if -> x\n",
        "f(x) if x if y -> x\n",
        "f(x) if x = 1 -> x\n",
        "f(x) -> x if x\n",
        "f : Nat if x -> Nat\n",
    ];
    for source in refused {
        assert!(!agree(&grammar, source, source), "{source} is refused");
    }
}

#[test]
fn a_choice_the_next_token_cannot_make_is_found() {
    let alike = Grammar::read("file = a | b ; a = NAME ; b = NAME TYPE ;");
    assert_eq!(alike.conflicts(), ["`file`: two branches begin alike"]);
    let greedy = Grammar::read("file = { NAME } NAME EOF ;");
    assert_eq!(
        greedy.conflicts(),
        ["`file`: an optional part begins as what follows it"]
    );
    let unused = Grammar::read("file = NAME ; other = TYPE ;");
    assert_eq!(unused.unreached(), ["other"]);
}
