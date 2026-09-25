//! A target's selected instructions, and the labels that tie them together.
//!
//! Every target that writes a flat sequence of instructions needs the same
//! things beside it: labels made before the code they name, bound to a
//! position once, and still naming the right instruction after others are
//! dropped. [`Code`] owns both, so no pass can move one without the other.
//! What an instruction is stays with its target: this only stores them.

use crate::index::index;

index!(pub Label);

/// Instructions in order, and the position each label is bound to.
///
/// A label stands before whatever comes next, so its position is the index
/// of the instruction after it, or the length where nothing does. Dropping
/// an instruction moves every label that stood before it to what that
/// instruction stood before.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Code<I> {
    insts: Vec<I>,
    labels: Vec<Option<usize>>,
    /// Where the label bound last stands. Labels are bound at the end, and
    /// dropping instructions never reorders them, so this is the furthest.
    last_bound: Option<usize>,
}

impl<I> Default for Code<I> {
    fn default() -> Self {
        Self {
            insts: Vec::new(),
            labels: Vec::new(),
            last_bound: None,
        }
    }
}

impl<I> Code<I> {
    /// A label, not yet bound anywhere.
    pub fn label(&mut self) -> Label {
        let label = Label::at(self.labels.len());
        self.labels.push(None);
        label
    }

    /// Bind a label before whatever is pushed next.
    ///
    /// # Panics
    ///
    /// If the label is already bound, or was made by other code.
    pub fn bind(&mut self, label: Label) {
        let position = &mut self.labels[label.index()];
        assert!(position.is_none(), "a label is bound once");
        *position = Some(self.insts.len());
        self.last_bound = *position;
    }

    pub fn push(&mut self, inst: I) {
        self.insts.push(inst);
    }

    #[must_use]
    pub fn insts(&self) -> &[I] {
        &self.insts
    }

    /// The instructions, to rewrite in place. Their count cannot change
    /// here, so no label moves.
    #[must_use]
    pub fn insts_mut(&mut self) -> &mut [I] {
        &mut self.insts
    }

    /// Where a label is bound, if it is.
    ///
    /// # Panics
    ///
    /// If the label was made by other code.
    #[must_use]
    pub fn position(&self, label: Label) -> Option<usize> {
        self.labels[label.index()]
    }

    /// Whether any label stands at `at` or after it.
    ///
    /// A rewrite of the instructions from `at` on must ask first: a jump to
    /// a label among them would skip part of what it replaced.
    #[must_use]
    pub fn labelled_from(&self, at: usize) -> bool {
        self.last_bound.is_some_and(|last| last >= at)
    }

    /// Every label made so far, with where it is bound.
    #[must_use]
    pub fn labels(&self) -> impl ExactSizeIterator<Item = (Label, Option<usize>)> + '_ {
        self.labels
            .iter()
            .enumerate()
            .map(|(at, &position)| (Label::at(at), position))
    }

    /// Drop the instruction at `at`, moving labels after it back by one.
    ///
    /// # Panics
    ///
    /// If there is no instruction at `at`.
    pub fn remove(&mut self, at: usize) -> I {
        let inst = self.insts.remove(at);
        for position in self
            .labels
            .iter_mut()
            .chain([&mut self.last_bound])
            .flatten()
        {
            if *position > at {
                *position -= 1;
            }
        }
        inst
    }

    /// Keep the instructions `kept` says to, in order, and move every label
    /// that stood before a dropped one.
    ///
    /// # Panics
    ///
    /// If `kept` does not say for every instruction.
    pub fn keep(&mut self, kept: &[bool]) {
        assert_eq!(kept.len(), self.insts.len(), "a keep for every instruction");
        if kept.iter().all(|&held| held) {
            return;
        }
        let mut moved = Vec::with_capacity(kept.len() + 1);
        let mut at = 0;
        for &held in kept {
            moved.push(at);
            at += usize::from(held);
        }
        moved.push(at);
        for position in self
            .labels
            .iter_mut()
            .chain([&mut self.last_bound])
            .flatten()
        {
            *position = moved[*position];
        }
        let mut held = kept.iter();
        self.insts
            .retain(|_| *held.next().expect("a keep for every instruction"));
    }
}

#[cfg(test)]
mod tests {
    use super::Code;

    #[test]
    fn a_dropped_instruction_leaves_its_labels_before_what_followed_it() {
        let mut code = Code::default();
        let first = code.label();
        let middle = code.label();
        let end = code.label();
        code.bind(first);
        code.push('a');
        code.bind(middle);
        code.push('b');
        code.push('c');
        code.bind(end);

        assert!(code.labelled_from(3) && !code.labelled_from(4));

        code.keep(&[true, false, true]);
        assert_eq!(code.insts(), ['a', 'c']);
        assert_eq!(code.position(first), Some(0));
        assert_eq!(code.position(middle), Some(1));
        assert_eq!(code.position(end), Some(2));

        assert_eq!(code.remove(0), 'a');
        assert_eq!(code.insts(), ['c']);
        assert_eq!(code.position(first), Some(0));
        assert_eq!(code.position(middle), Some(0));
        assert_eq!(code.position(end), Some(1));
        assert!(code.labelled_from(1) && !code.labelled_from(2));
    }

    #[test]
    #[should_panic(expected = "a label is bound once")]
    fn a_label_is_bound_once() {
        let mut code = Code::<u8>::default();
        let label = code.label();
        code.bind(label);
        code.bind(label);
    }
}
