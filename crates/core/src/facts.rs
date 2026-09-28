//! What is known about a value, said once for every tier that reads one.
//!
//! Barb works these out, machine IR carries them as the class a value is
//! held at, and a target reads them to decide how many bytes a value takes
//! and whether anything has to be taken off it. Said here rather than in
//! any of the three, because a fact said twice in two vocabularies is two
//! facts that have to agree and nothing checking that they do.
//!
//! Today this is an interval. What else is worth knowing -- which bits are
//! certainly nought, whether a value is certainly not nought -- belongs
//! beside it rather than instead of it: an interval answers what a
//! comparison decides, and a bit pattern answers what a mask does, and
//! neither answers the other.

/// The least and greatest a number can be. No greatest is a number counting
/// up without a last step, which is every `Nat` until something says less.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Facts {
    pub low: u64,
    pub high: Option<u64>,
}

impl Facts {
    /// Nothing is known, so anything is possible.
    pub const ANY: Self = Self { low: 0, high: None };

    /// And no number at all, which is where a walk starts: a name nothing
    /// has reached yet holds nothing, rather than holding anything. Starting
    /// at anything would be sound and would stay there, since what is known
    /// only ever grows.
    pub const NOTHING: Self = Self {
        low: 1,
        high: Some(0),
    };

    #[must_use]
    pub const fn is_nothing(self) -> bool {
        matches!(self.high, Some(high) if high < self.low)
    }

    /// Exactly this.
    #[must_use]
    pub const fn at(value: u64) -> Self {
        Self {
            low: value,
            high: Some(value),
        }
    }

    /// Either of two, which is what a match holds where its arms disagree.
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        if self.is_nothing() {
            return other;
        }
        if other.is_nothing() {
            return self;
        }
        Self {
            low: self.low.min(other.low),
            high: self.high.zip(other.high).map(|(a, b)| a.max(b)),
        }
    }

    /// One more, which is what a constructor of a number answers.
    #[must_use]
    pub fn up(self) -> Self {
        if self.is_nothing() {
            return self;
        }
        Self {
            low: self.low.saturating_add(1),
            high: self.high.and_then(|high| high.checked_add(1)),
        }
    }

    /// One less, stopping at nought, which is what taking one apart holds.
    #[must_use]
    pub fn down(self) -> Self {
        if self.is_nothing() {
            return self;
        }
        Self {
            low: self.low.saturating_sub(1),
            high: self.high.map(|high| high.saturating_sub(1)),
        }
    }

    /// Both together, which is what adding them answers.
    #[must_use]
    pub fn plus(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        Self {
            low: self.low.saturating_add(other.low),
            high: self
                .high
                .zip(other.high)
                .and_then(|(a, b)| a.checked_add(b)),
        }
    }

    /// The intersection is what a branch establishes in addition to its input.
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self {
            low: self.low.max(other.low),
            high: match (self.high, other.high) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
        }
    }

    #[must_use]
    pub fn monus(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        Self {
            low: other.high.map_or(0, |b| self.low.saturating_sub(b)),
            high: self.high.map(|a| a.saturating_sub(other.low)),
        }
    }

    #[must_use]
    pub fn times(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if self.high == Some(0) || other.high == Some(0) {
            return Self::at(0);
        }
        Self {
            low: self.low.saturating_mul(other.low),
            high: self
                .high
                .zip(other.high)
                .and_then(|(a, b)| a.checked_mul(b)),
        }
    }

    #[must_use]
    pub fn quotient(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if other.high == Some(0) {
            return Self::at(0);
        }
        Self {
            low: if other.low == 0 {
                0
            } else {
                other.high.map_or(0, |b| self.low / b)
            },
            high: self.high.map(|a| a / other.low.max(1)),
        }
    }

    #[must_use]
    pub fn remainder(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if other.high == Some(0) {
            return self;
        }
        let high = if other.low == 0 {
            self.high
        } else {
            match (self.high, other.high.map(|b| b.saturating_sub(1))) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            }
        };
        Self { low: 0, high }
    }

    /// What a bitwise and of the two can be: no bit either lacks, so no
    /// more than the smaller.
    #[must_use]
    pub fn masked(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        Self {
            low: 0,
            high: match (self.high, other.high) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
        }
    }

    /// What a bitwise or, or exclusive or, of the two can be: no bit above
    /// the wider's highest. `at_least` is whether the answer is at least
    /// each operand, as an or's is and an exclusive or's is not.
    #[must_use]
    pub fn merged(self, other: Self, at_least: bool) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        let high = self.high.zip(other.high).map(|(a, b)| {
            let widest = a.max(b);
            u64::MAX.checked_shr(widest.leading_zeros()).unwrap_or(0)
        });
        Self {
            low: if at_least { self.low.max(other.low) } else { 0 },
            high,
        }
    }

    /// What the first to the power of the second can be: at least one
    /// where the base is, and no more than the greatest base to the
    /// greatest exponent.
    #[must_use]
    pub fn power(self, exponent: Self) -> Self {
        if self.is_nothing() || exponent.is_nothing() {
            return Self::NOTHING;
        }
        let high = match self.high {
            // Nought to the nought is one, and to anything else nought.
            Some(0 | 1) => Some(1),
            Some(base) => exponent
                .high
                .and_then(|exponent| u32::try_from(exponent).ok())
                .and_then(|exponent| base.checked_pow(exponent)),
            None => None,
        };
        Self {
            low: u64::from(self.low > 0),
            high,
        }
    }

    /// How many bits hold every number this could be, where anything does.
    #[must_use]
    pub fn width(self) -> Option<u16> {
        // A `u64` needs at most sixty-four bits, so the count is one a
        // `u16` holds however big the number is.
        let high = self.high?;
        u16::try_from(u64::BITS - high.leading_zeros()).ok()
    }

    /// Whether nothing this can be is above anything that one can be.
    ///
    /// This is what says a value is already something the other admits:
    /// what a place has to hold is the greatest that reaches it, and a
    /// least says nothing about that. A value that might be nought where
    /// something expects at least two is still a value that place holds.
    #[must_use]
    pub const fn no_higher_than(self, other: Self) -> bool {
        match (self.high, other.high) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(held), Some(other)) => held <= other,
        }
    }

    /// Whether this says less than `other` does, which is what says a walk
    /// has settled.
    #[must_use]
    pub const fn within(self, other: Self) -> bool {
        if self.is_nothing() {
            return true;
        }
        if other.is_nothing() {
            return false;
        }
        self.low >= other.low
            && match (self.high, other.high) {
                (_, None) => true,
                (None, Some(_)) => false,
                (Some(held), Some(other)) => held <= other,
            }
    }
}
