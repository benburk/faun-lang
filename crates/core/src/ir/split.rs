//! Splitting numbers wider than a word into words.
//!
//! Before a target is chosen, a number known to fit sixty-four bits is a
//! fixed width however wide its target's word is, since what a word holds is
//! the target's to say. A target whose word is narrower holds each such
//! number as as many words as it needs, the least significant first: here
//! every value, parameter, result and field of one becomes that many words,
//! and every instruction reading or writing one does so a word at a time.
//! Nothing is put on the heap, and a number that fits a word is untouched.
//!
//! A sum and a difference go word to word, carrying; a product is the
//! schoolbook one, kept to as many words as the result is known to need; an
//! order is decided from the most significant word down; a shift moves whole
//! words and the bits between them. A quotient and a remainder, which are
//! rare this wide, go through a natural and back.
//!
//! The logical entry and external routines keep their signatures: a target
//! hands the entry what fits its word, and a routine reads what it reads.

use num_bigint::BigUint;

use crate::index::append_range;

use super::digits::{add_carry, mul_wide, sub_borrow};
use super::rewrite::{self, Declarations, Rebuild};
use super::{
    Binary, Builder, Class, Direction, Exit, FunctionId, Op, Program, Range, Relation, ShapeId,
    Terminator, ValueId,
};

const W: Class = Class::Word;

/// Rebuild `source` so that nothing is held wider than a word of
/// `word_bits`. A program with nothing that wide is returned as it stands.
#[must_use]
pub fn split(source: &Program, word_bits: u16) -> Program {
    let widths = Widths { word_bits };
    let wide = |class: &Class| widths.words(*class) > 1;
    if !source.classes.iter().any(wide) && !source.signature.iter().any(wide) {
        return source.clone();
    }
    let declared = declarations(source, widths);
    let mut pass = Split {
        widths,
        wide: vec![None; source.values_count()],
        yields: Vec::new(),
        loops: Vec::new(),
        returns: Vec::new(),
    };
    rewrite::rebuild_declared(source, declared, &mut pass)
}

/// How many words a target of `word_bits` holds each class in.
#[derive(Clone, Copy)]
struct Widths {
    word_bits: u16,
}

impl Widths {
    /// One, but for a fixed width wider than a word: as many words as it
    /// needs.
    fn words(self, class: Class) -> usize {
        match class {
            Class::Held(_) => class
                .width()
                .filter(|&bits| bits > self.word_bits)
                .map_or(1, |bits| usize::from(bits.div_ceil(self.word_bits))),
            _ => 1,
        }
    }

    /// `classes`, each wide one as its words.
    fn expanded(self, classes: &[Class]) -> Vec<Class> {
        classes
            .iter()
            .flat_map(|&class| match self.words(class) {
                1 => vec![class],
                n => vec![W; n],
            })
            .collect()
    }
}

/// A sum, a difference or a monus of the words `x` and `y`, word to word,
/// carrying or borrowing. A monus is nought where the right was the larger:
/// every word times one where nothing was left owing.
fn carried(b: &mut Builder, op: Binary, x: &[ValueId], y: &[ValueId]) -> Vec<ValueId> {
    let mut carry = b.constant(W, 0);
    let mut out = Vec::with_capacity(x.len());
    for (&x, &y) in x.iter().zip(y) {
        let (word, next) = if op == Binary::Add {
            add_carry(b, x, y, carry)
        } else {
            sub_borrow(b, x, y, carry)
        };
        out.push(word);
        carry = next;
    }
    if op == Binary::Monus {
        let one = b.constant(W, 1);
        let kept = b.binary(Binary::Sub, one, carry);
        out = out
            .into_iter()
            .map(|word| b.binary(Binary::Mul, word, kept))
            .collect();
    }
    out
}

/// Every declaration, with each defined function's wide parameters and
/// results as their words. The pools are written afresh.
fn declarations(source: &Program, widths: Widths) -> Declarations {
    let mut declared = Declarations::of(source);
    declared.signature.clear();
    declared.parameters.clear();
    for id in source.functions.ids() {
        let function = &mut declared.functions[id];
        let splits = function.external().is_none();
        let params = source.signature(function.params);
        let names = &source.parameters[function.parameters.range()];
        let (classes, names): (Vec<_>, Vec<_>) = if splits {
            params
                .iter()
                .zip(names)
                .flat_map(|(&class, &name)| {
                    let n = widths.words(class);
                    let class = if n == 1 { class } else { W };
                    std::iter::repeat_n((class, name), n)
                })
                .unzip()
        } else {
            (params.to_vec(), names.to_vec())
        };
        function.params = append_range(&mut declared.signature, &classes);
        function.parameters = append_range(&mut declared.parameters, &names);
        if let super::Returns::Values(returns) = function.returns {
            let returns = source.signature(returns);
            let returns = if splits {
                widths.expanded(returns)
            } else {
                returns.to_vec()
            };
            function.returns =
                super::Returns::Values(append_range(&mut declared.signature, &returns));
        }
    }
    declared
}

struct Split {
    widths: Widths,
    /// The words each wide value of the old program is, least significant
    /// first. The first also stands for it, for whatever copies an
    /// instruction naming it, which is never one reading all of it.
    wide: Vec<Option<Vec<ValueId>>>,
    /// The classes each enclosing `if`'s arms yield, innermost last.
    yields: Vec<Vec<Class>>,
    /// The classes each enclosing loop continues and breaks with.
    loops: Vec<(Vec<Class>, Vec<Class>)>,
    /// The classes the function being rebuilt answers.
    returns: Vec<Class>,
}

impl Split {
    const fn word_bits(&self) -> u16 {
        self.widths.word_bits
    }

    /// Say that the old value `old` is the words `words`.
    fn put(&mut self, rebuild: &Rebuild<'_>, old: ValueId, words: Vec<ValueId>) {
        rebuild.stands_for(old, words[0]);
        self.wide[old.index()] = Some(words);
    }

    /// Say that each of `olds`, at `classes`, is what `fresh` holds in turn:
    /// one value, or a wide one's words.
    fn grouped(
        &mut self,
        rebuild: &Rebuild<'_>,
        olds: &[ValueId],
        classes: &[Class],
        fresh: &[ValueId],
    ) {
        let mut at = 0;
        for (&old, &class) in olds.iter().zip(classes) {
            let n = self.widths.words(class);
            if n == 1 {
                rebuild.stands_for(old, fresh[at]);
            } else {
                self.put(rebuild, old, fresh[at..at + n].to_vec());
            }
            at += n;
        }
    }

    /// What stands for each of `olds` where a region opens with `fresh`,
    /// recording each wide one's words.
    fn opened(&mut self, olds: &[ValueId], classes: &[Class], fresh: &[ValueId]) -> Vec<ValueId> {
        let mut at = 0;
        let mut standing = Vec::with_capacity(olds.len());
        for (&old, &class) in olds.iter().zip(classes) {
            let n = self.widths.words(class);
            if n > 1 {
                self.wide[old.index()] = Some(fresh[at..at + n].to_vec());
            }
            standing.push(fresh[at]);
            at += n;
        }
        standing
    }

    /// The old value `old` as `n` words: its own words, or the one value it
    /// is, each padded with noughts or cut to `n`.
    fn words(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        old: ValueId,
        n: usize,
    ) -> Vec<ValueId> {
        let mut words = self.wide[old.index()].clone().unwrap_or_else(|| {
            let value = rebuild.value(old);
            let word = if b.class(value) == W {
                value
            } else {
                b.convert(W, value)
            };
            vec![word]
        });
        words.truncate(n);
        while words.len() < n {
            words.push(b.constant(W, 0));
        }
        words
    }

    /// What `values` become where they go to `classes`: each wide one's
    /// words, and each other as it is, at the class it goes to where that
    /// differs, as a loop's first state is.
    fn crossing(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        values: &[ValueId],
        classes: &[Class],
    ) -> Vec<ValueId> {
        let mut out = Vec::new();
        for (&old, &class) in values.iter().zip(classes) {
            match self.widths.words(class) {
                1 => out.push(rebuild.value(old)),
                n => out.extend(self.words(rebuild, b, old, n)),
            }
        }
        out
    }

    fn wide(&self, rebuild: &Rebuild<'_>, value: ValueId) -> bool {
        self.widths.words(rebuild.source().class(value)) > 1
    }

    /// A wide value held as a natural, most significant word first.
    fn natural(&self, b: &mut Builder, words: &[ValueId]) -> ValueId {
        let base = b.natural(&(BigUint::from(1u8) << usize::from(self.word_bits())));
        let (last, rest) = words.split_last().expect("a wide value has words");
        let mut n = b.convert(Class::Natural, *last);
        for &word in rest.iter().rev() {
            n = b.binary(Binary::Mul, n, base);
            let word = b.convert(Class::Natural, word);
            n = b.binary(Binary::Add, n, word);
        }
        n
    }

    /// The low `count` words of a natural: each its low word, then the rest
    /// divided by the base, in two divisions by words so each is short.
    fn natural_words(&self, b: &mut Builder, natural: ValueId, count: usize) -> Vec<ValueId> {
        let half = b.constant(W, 1 << (self.word_bits() - 1));
        let half = b.convert(Class::Natural, half);
        let two = b.constant(W, 2);
        let two = b.convert(Class::Natural, two);
        let mut rest = natural;
        let mut words = Vec::with_capacity(count);
        for at in 0..count {
            words.push(b.convert(W, rest));
            if at + 1 < count {
                rest = b.binary(Binary::Div, rest, half);
                rest = b.binary(Binary::Div, rest, two);
            }
        }
        words
    }

    /// Words, as a value of `class`: its words where it is wide, and
    /// otherwise the lowest, which is all of it.
    fn result(&self, b: &mut Builder, words: &[ValueId], class: Class) -> Vec<ValueId> {
        match self.widths.words(class) {
            1 if class == W => vec![words[0]],
            1 => vec![b.convert(class, words[0])],
            n => words[..n].to_vec(),
        }
    }

    fn binary(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (op, left, right): (Binary, ValueId, ValueId),
        class: Class,
    ) -> Vec<ValueId> {
        let source = rebuild.source();
        let own = self.widths.words(class);
        let all = own
            .max(self.widths.words(source.class(left)))
            .max(self.widths.words(source.class(right)));
        // A result is known to fit its class, so a sum, a difference and a
        // product need only its words; a monus asks which is larger first.
        let n = if op == Binary::Monus { all } else { own };
        let words = match op {
            Binary::Add | Binary::Sub | Binary::Monus => {
                let x = self.words(rebuild, b, left, n);
                let y = self.words(rebuild, b, right, n);
                carried(b, op, &x, &y)
            }
            Binary::Mul => {
                let x = self.words(rebuild, b, left, n);
                let y = self.words(rebuild, b, right, n);
                self.product(b, &x, &y)
            }
            Binary::Div | Binary::Mod => {
                let x = self.words(rebuild, b, left, all);
                self.divided(rebuild, b, (op, &x, right), (own, all))
            }
            Binary::ShiftUp | Binary::ShiftDown => {
                unreachable!("a shift wider than a word is expanded before splitting")
            }
            // Each word of the answer is the same words' answer.
            Binary::And | Binary::Or | Binary::Xor => {
                let x = self.words(rebuild, b, left, n);
                let y = self.words(rebuild, b, right, n);
                x.iter()
                    .zip(&y)
                    .map(|(&x, &y)| b.binary(op, x, y))
                    .collect()
            }
        };
        self.result(b, &words, class)
    }

    /// `x` divided by `right`, the quotient or remainder `op` asks, as `own`
    /// words: by short division where the divisor fits half a word, and
    /// otherwise through a natural.
    fn divided(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (op, x, right): (Binary, &[ValueId], ValueId),
        (own, all): (usize, usize),
    ) -> Vec<ValueId> {
        let short = rebuild
            .source()
            .class(right)
            .width()
            .is_some_and(|bits| bits <= self.word_bits() / 2);
        if !short {
            let y = self.words(rebuild, b, right, all);
            let x = self.natural(b, x);
            let y = self.natural(b, &y);
            let answer = b.binary(op, x, y);
            return self.natural_words(b, answer, own);
        }
        let d = rebuild.value(right);
        let d = if b.class(d) == W { d } else { b.convert(W, d) };
        let (quotient, left) = self.short(b, x, d);
        if op == Binary::Div {
            return quotient;
        }
        // What is left fits a word, but by nought it is all of `x`, as a
        // remainder by nought is.
        let zero = b.constant(W, 0);
        let by_nought = b.compare(Relation::Equal, d, zero);
        let one = b.constant(W, 1);
        let by_some = b.binary(Binary::Sub, one, by_nought);
        x.iter()
            .enumerate()
            .map(|(at, &word)| {
                let whole = b.binary(Binary::Mul, word, by_nought);
                if at == 0 {
                    let kept = b.binary(Binary::Mul, left, by_some);
                    b.binary(Binary::Add, kept, whole)
                } else {
                    whole
                }
            })
            .collect()
    }

    /// The words of `x` divided by `d`, which fits half a word, and what is
    /// left: half a word at a time from the top, so each step divides what
    /// is left, below `d`, and the next half word, which together fit a
    /// word. By nought each step answers nought, as a word's quotient does,
    /// and what is left is not the remainder, which the caller makes `x`.
    fn short(&self, b: &mut Builder, x: &[ValueId], d: ValueId) -> (Vec<ValueId>, ValueId) {
        let bits = self.word_bits() / 2;
        let base = b.constant(W, 1 << bits);
        let mut left = b.constant(W, 0);
        let mut quotient = vec![left; x.len()];
        for (at, &word) in x.iter().enumerate().rev() {
            let high = b.shift(W, Direction::Down, word, bits);
            let low = b.binary(Binary::Mod, word, base);
            let mut halves = [left; 2];
            for (half, part) in [(1, high), (0, low)] {
                let lifted = b.shift(W, Direction::Up, left, bits);
                let current = b.binary(Binary::Add, lifted, part);
                halves[half] = b.binary(Binary::Div, current, d);
                left = b.binary(Binary::Mod, current, d);
            }
            let upper = b.shift(W, Direction::Up, halves[1], bits);
            quotient[at] = b.binary(Binary::Add, upper, halves[0]);
        }
        (quotient, left)
    }

    /// The low `x.len()` words of `x * y`, the schoolbook way.
    fn product(&self, b: &mut Builder, x: &[ValueId], y: &[ValueId]) -> Vec<ValueId> {
        let n = x.len();
        let zero = b.constant(W, 0);
        let mut out = vec![zero; n];
        for (i, &xi) in x.iter().enumerate() {
            let mut carry = zero;
            for (j, &yj) in y.iter().enumerate().take(n - i) {
                let (low, high) = mul_wide(b, xi, yj, self.word_bits());
                let (sum, carried) = add_carry(b, out[i + j], low, carry);
                out[i + j] = sum;
                carry = b.binary(Binary::Add, high, carried);
            }
        }
        out
    }

    fn compare(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (relation, left, right): (Relation, ValueId, ValueId),
    ) -> ValueId {
        let source = rebuild.source();
        let n = self
            .widths
            .words(source.class(left))
            .max(self.widths.words(source.class(right)));
        let x = self.words(rebuild, b, left, n);
        let y = self.words(rebuild, b, right, n);
        let mut answer = b.constant(W, u64::from(relation == Relation::Equal));
        for (&x, &y) in x.iter().zip(&y) {
            let same = b.compare(Relation::Equal, x, y);
            answer = match relation {
                // Equal where every word is.
                Relation::Equal => b.binary(Binary::Mul, answer, same),
                // Less where this word is, or where it is the same and what
                // is below it is: words taken from the least up.
                Relation::Less => {
                    let less = b.compare(Relation::Less, x, y);
                    let below = b.binary(Binary::Mul, same, answer);
                    b.binary(Binary::Add, less, below)
                }
            };
        }
        answer
    }

    fn shift(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (direction, value, by): (Direction, ValueId, u16),
        class: Class,
    ) -> Vec<ValueId> {
        let bits = self.word_bits();
        let from = self.widths.words(rebuild.source().class(value));
        let own = self.widths.words(class);
        let words = self.words(rebuild, b, value, from);
        let (whole, part) = (usize::from(by / bits), by % bits);
        let word = |b: &mut Builder, at: Option<usize>| {
            at.and_then(|at| words.get(at).copied())
                .unwrap_or_else(|| b.constant(W, 0))
        };
        let out: Vec<_> = (0..own)
            .map(|i| {
                let (near, far) = match direction {
                    Direction::Up => (i.checked_sub(whole), i.checked_sub(whole + 1)),
                    Direction::Down => (Some(i + whole), Some(i + whole + 1)),
                };
                let near = word(b, near);
                if part == 0 {
                    return near;
                }
                let far = word(b, far);
                let (near, far) = match direction {
                    Direction::Up => (
                        b.shift(W, Direction::Up, near, part),
                        b.shift(W, Direction::Down, far, bits - part),
                    ),
                    Direction::Down => (
                        b.shift(W, Direction::Down, near, part),
                        b.shift(W, Direction::Up, far, bits - part),
                    ),
                };
                b.binary(Binary::Add, near, far)
            })
            .collect();
        self.result(b, &out, class)
    }

    fn convert(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        value: ValueId,
        class: Class,
    ) -> Vec<ValueId> {
        let from = rebuild.source().class(value);
        let own = self.widths.words(class);
        if class == Class::Natural {
            let n = self.widths.words(from);
            let words = self.words(rebuild, b, value, n);
            return vec![self.natural(b, &words)];
        }
        if from == Class::Natural {
            let words = self.natural_words(b, rebuild.value(value), own);
            return self.result(b, &words, class);
        }
        let mut words = self.words(rebuild, b, value, own);
        // Read at a narrower width, a number is what that width holds of
        // it: the top word keeps only the bits the class has.
        if own > 1
            && let Some(bits) = class.width()
        {
            let spare = u16::try_from(own).expect("few words") * self.word_bits() - bits;
            if spare > 0 {
                let top = words[own - 1];
                let kept = b.shift(W, Direction::Up, top, spare);
                words[own - 1] = b.shift(W, Direction::Down, kept, spare);
            }
        }
        self.result(b, &words, class)
    }

    /// `shape` with each wide leaf as its words, and where each old leaf
    /// begins in it; nothing where no leaf is wide.
    fn shape(
        &self,
        b: &mut Builder,
        source: &Program,
        shape: ShapeId,
    ) -> Option<(ShapeId, Vec<u32>)> {
        let classes = source.shaped(shape);
        if classes.iter().all(|&class| self.widths.words(class) == 1) {
            return None;
        }
        let mut starts = Vec::with_capacity(classes.len());
        let mut at = 0u32;
        for &class in classes {
            starts.push(at);
            at += u32::try_from(self.widths.words(class)).expect("few words");
        }
        Some((b.shape(&self.widths.expanded(classes)), starts))
    }

    /// A field of an object or element of `shape` as `read` answers each
    /// leaf of its split shape: one value, or a wide one's words.
    fn field(
        &self,
        (class, index): (Class, u32),
        (shape, starts): (ShapeId, &[u32]),
        read: &mut dyn FnMut((Class, ShapeId), u32) -> ValueId,
    ) -> Vec<ValueId> {
        let start = starts[usize::try_from(index).expect("an index fits")];
        match self.widths.words(class) {
            1 => vec![read((class, shape), start)],
            n => (start..).take(n).map(|at| read((W, shape), at)).collect(),
        }
    }

    /// The fields handed to an object or element of `shape`, each wide one
    /// as its words.
    fn fields(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        fields: &[ValueId],
        shape: ShapeId,
    ) -> Vec<ValueId> {
        let classes = rebuild.source().shaped(shape).to_vec();
        self.crossing(rebuild, b, fields, &classes)
    }

    /// An instruction holding a shape with a wide leaf, written with its
    /// split shape: what it answers, or nothing where no leaf is wide.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per instruction holding a shape"
    )]
    fn shaped(&self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op) -> Option<Vec<ValueId>> {
        let source = rebuild.source();
        let v = |old| rebuild.value(old);
        let split = |b: &mut Builder, shape| self.shape(b, source, shape);
        Some(match op {
            Op::Cell { tag, fields, shape } => {
                let (split, _) = split(b, shape)?;
                let fields = self.fields(rebuild, b, source.values(fields), shape);
                vec![b.cell(tag, split, &fields)]
            }
            Op::CellField { cell, index, shape } => {
                let (split, starts) = split(b, shape)?;
                let cell = v(cell);
                let class = source.shaped(shape)[usize::try_from(index).expect("fits")];
                self.field((class, index), (split, &starts), &mut |held, at| {
                    b.cell_field(held, cell, at)
                })
            }
            Op::BufferField {
                buffer,
                start,
                index,
                shape,
            } => {
                let (split, starts) = split(b, shape)?;
                let at_buffer = (v(buffer), v(start));
                let class = source.shaped(shape)[usize::try_from(index).expect("fits")];
                self.field((class, index), (split, &starts), &mut |held, at| {
                    b.buffer_field(held, at_buffer, at)
                })
            }
            Op::BufferPush { operands, shape } => {
                let (split, _) = split(b, shape)?;
                let operands = source.values(operands);
                let (sequence, fields) = operands.split_at(3);
                let fields = self.fields(rebuild, b, fields, shape);
                b.buffer_push(
                    (v(sequence[0]), v(sequence[1]), v(sequence[2])),
                    split,
                    &fields,
                )
                .to_vec()
            }
            Op::BufferReplace { operands, shape } => {
                let (split, _) = split(b, shape)?;
                let operands = source.values(operands);
                let (sequence, fields) = operands.split_at(4);
                let fields = self.fields(rebuild, b, fields, shape);
                b.buffer_replace(
                    (v(sequence[0]), v(sequence[1]), v(sequence[2])),
                    v(sequence[3]),
                    split,
                    &fields,
                )
                .to_vec()
            }
            Op::BufferEmpty { shape } => {
                let (split, _) = split(b, shape)?;
                vec![b.buffer_empty(split)]
            }
            // Each wide leaf of each element laid out as its words, a word's
            // bytes a leaf.
            Op::BufferKnown {
                elements,
                shape,
                bytes,
            } => {
                let (split, _) = split(b, shape)?;
                let classes = source.shaped(shape);
                let word = self.word_bits() / 8;
                let leaves: Vec<_> =
                    super::model::known_leaves(source.datum_bytes(elements), bytes).collect();
                let mut laid = Vec::new();
                for element in leaves.chunks(classes.len()) {
                    for (&class, &value) in classes.iter().zip(element) {
                        for at in 0..self.widths.words(class) {
                            let shift =
                                u32::from(self.word_bits()) * u32::try_from(at).expect("few");
                            let piece = value.checked_shr(shift).unwrap_or(0);
                            laid.extend_from_slice(&piece.to_le_bytes()[..usize::from(word)]);
                        }
                    }
                }
                let data = b.data(&laid);
                let bytes = u8::try_from(word).expect("a word of at most eight bytes");
                vec![b.buffer_known(data, split, bytes)]
            }
            Op::BufferPrepend { operands, shape } | Op::BufferExtend { operands, shape } => {
                let (split, _) = split(b, shape)?;
                let o = rebuild.args(operands);
                let (first, then) = ((o[0], o[1], o[2]), (o[3], o[4], o[5]));
                let answered = if matches!(op, Op::BufferPrepend { .. }) {
                    b.buffer_prepend(first, then, split)
                } else {
                    b.buffer_extend(first, then, split)
                };
                answered.to_vec()
            }
            Op::BufferRoom { count, shape } => {
                let (split, _) = split(b, shape)?;
                vec![b.buffer_room(v(count), split)]
            }
            Op::BufferAt {
                buffer,
                start,
                shape,
            } => {
                let (split, _) = split(b, shape)?;
                vec![b.buffer_at((v(buffer), v(start)), split)]
            }
            _ => return None,
        })
    }

    /// A constant as `n` words.
    fn constant(&self, b: &mut Builder, value: u64, n: usize) -> Vec<ValueId> {
        let bits = self.word_bits();
        (0..n)
            .map(|at| {
                let shift = u32::from(bits) * u32::try_from(at).expect("few words");
                let word = value.checked_shr(shift).unwrap_or(0);
                b.constant(W, word & (u64::MAX >> (64 - bits)))
            })
            .collect()
    }

    /// A number instruction reading or writing a wide value, a word at a
    /// time: what it answers, or nothing where none is wide.
    fn numeric(
        &self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> Option<Vec<ValueId>> {
        let source = rebuild.source();
        let result_class = results.first().map(|&result| source.class(result));
        let wide_result = results.iter().any(|&result| self.wide(rebuild, result));
        Some(match op {
            Op::Constant { value } if wide_result => {
                let n = self.widths.words(source.class(results[0]));
                self.constant(b, value, n)
            }
            Op::Convert { value } if wide_result || self.wide(rebuild, value) => {
                let class = result_class.expect("a conversion answers");
                self.convert(rebuild, b, value, class)
            }
            Op::Binary { op, left, right }
                if wide_result || self.wide(rebuild, left) || self.wide(rebuild, right) =>
            {
                let class = result_class.expect("arithmetic answers");
                self.binary(rebuild, b, (op, left, right), class)
            }
            Op::Compare {
                relation,
                left,
                right,
            } if self.wide(rebuild, left) || self.wide(rebuild, right) => {
                vec![self.compare(rebuild, b, (relation, left, right))]
            }
            Op::Shift {
                direction,
                value,
                by,
            } if wide_result || self.wide(rebuild, value) => {
                let class = result_class.expect("a shift answers");
                self.shift(rebuild, b, (direction, value, by), class)
            }
            _ => return None,
        })
    }

    fn call(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (function, args): (FunctionId, Range),
        results: &[ValueId],
    ) {
        let source = rebuild.source();
        let declared = source.function(function);
        let params = source.signature(declared.params).to_vec();
        let args = self.crossing(rebuild, b, source.values(args), &params);
        let answered = b.call(function, &args);
        let classes = declared.returns.classes();
        let classes = source.signature(classes).to_vec();
        self.grouped(rebuild, results, &classes, &answered);
    }

    fn if_(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (condition, then_region, else_region): (ValueId, super::RegionId, super::RegionId),
        results: &[ValueId],
    ) {
        let classes = rebuild.classes(results);
        self.yields.push(classes.clone());
        let expanded = self.widths.expanded(&classes);
        let answered = {
            let pass = std::cell::RefCell::new(&mut *self);
            b.if_(
                rebuild.value(condition),
                &expanded,
                |b| rebuild.region(b, then_region, &[], &mut **pass.borrow_mut()),
                |b| rebuild.region(b, else_region, &[], &mut **pass.borrow_mut()),
            )
        };
        self.yields.pop();
        self.grouped(rebuild, results, &classes, &answered);
    }

    fn loop_(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        (initial, body): (Range, super::RegionId),
        results: &[ValueId],
    ) {
        let source = rebuild.source();
        let olds = source.values(source.region(body).params).to_vec();
        let state: Vec<_> = olds.iter().map(|&param| source.class(param)).collect();
        let initial: Vec<_> = source
            .values(initial)
            .iter()
            .zip(&state)
            .flat_map(|(&value, &class)| match self.widths.words(class) {
                // A loop goes round at the classes it was written with.
                1 => {
                    let value = rebuild.value(value);
                    vec![if b.class(value) == class {
                        value
                    } else {
                        b.convert(class, value)
                    }]
                }
                n => self.words(rebuild, b, value, n),
            })
            .collect();
        let classes = rebuild.classes(results);
        self.loops.push((state.clone(), classes.clone()));
        let answered = b.loop_(&initial, &self.widths.expanded(&classes), |b, params| {
            let standing = self.opened(&olds, &state, params);
            rebuild.region(b, body, &standing, self);
        });
        self.loops.pop();
        self.grouped(rebuild, results, &classes, &answered);
    }
}

impl rewrite::Pass for Split {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let source = rebuild.source();
        let wide_result = results.iter().any(|&result| self.wide(rebuild, result));
        let fresh = match op {
            // Every region is walked here, so each exit knows where it goes.
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                self.if_(rebuild, b, (condition, then_region, else_region), results);
                return true;
            }
            Op::Loop { initial, body } => {
                self.loop_(rebuild, b, (initial, body), results);
                return true;
            }
            Op::Call { function, args } if source.function(function).external().is_none() => {
                self.call(rebuild, b, (function, args), results);
                return true;
            }
            Op::Load { .. } | Op::Store { .. } | Op::Float { .. } => {
                assert!(
                    !wide_result && !source.operands(&op).any(|v| self.wide(rebuild, v)),
                    "nothing wider than a word is loaded, stored or computed as a float"
                );
                return false;
            }
            _ => match self
                .numeric(rebuild, b, op, results)
                .or_else(|| self.shaped(rebuild, b, op))
            {
                Some(fresh) => fresh,
                None => return false,
            },
        };
        let classes = rebuild.classes(results);
        self.grouped(rebuild, results, &classes, &fresh);
        true
    }

    fn enter(
        &mut self,
        rebuild: &Rebuild<'_>,
        _b: &mut Builder,
        function: FunctionId,
        params: &[ValueId],
    ) -> Vec<ValueId> {
        let source = rebuild.source();
        let declared = source.function(function);
        let body = declared.body().expect("a function entered has a body");
        let olds = source.values(source.region(body).params).to_vec();
        let classes = source.signature(declared.params).to_vec();
        self.returns = source.signature(declared.returns.classes()).to_vec();
        self.yields.clear();
        self.loops.clear();
        self.opened(&olds, &classes, params)
    }

    fn exit(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, terminator: Terminator) -> bool {
        let classes = match terminator.exit {
            Exit::Return => self.returns.clone(),
            Exit::Yield => self.yields.last().cloned().unwrap_or_default(),
            Exit::Continue => self
                .loops
                .last()
                .map(|(state, _)| state.clone())
                .unwrap_or_default(),
            Exit::Break => self
                .loops
                .last()
                .map(|(_, out)| out.clone())
                .unwrap_or_default(),
        };
        let values = rebuild.source().values(terminator.values).to_vec();
        let values = self.crossing(rebuild, b, &values, &classes);
        match terminator.exit {
            Exit::Return => b.ret(&values),
            Exit::Yield => b.yield_(&values),
            Exit::Continue => b.continue_(&values),
            Exit::Break => b.break_(&values),
        }
        true
    }
}
