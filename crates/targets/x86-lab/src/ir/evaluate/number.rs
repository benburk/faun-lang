//! The interpreter's numbers: a word held in place while it fits one, and
//! a `BigUint` only past that. Almost every value a program makes is a word,
//! and a `BigUint` for each is an allocation at every read.

use num_bigint::BigUint;

/// `Big` holds only what `Small` cannot, so that a number has one form and
/// the derived order is the numeric one: every `Small` is below every `Big`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Number {
    Small(u64),
    Big(Box<BigUint>),
}

impl Number {
    pub(super) const ZERO: Self = Self::Small(0);

    pub(super) fn big(value: BigUint) -> Self {
        u64::try_from(&value).map_or_else(|_| Self::Big(Box::new(value)), Self::Small)
    }

    pub(super) fn to_big(&self) -> BigUint {
        match self {
            Self::Small(n) => BigUint::from(*n),
            Self::Big(n) => (**n).clone(),
        }
    }

    pub(super) fn bits(&self) -> u64 {
        match self {
            Self::Small(n) => u64::from(u64::BITS - n.leading_zeros()),
            Self::Big(n) => n.bits(),
        }
    }

    pub(super) const fn is_zero(&self) -> bool {
        matches!(self, Self::Small(0))
    }

    pub(super) const fn small(&self) -> Option<u64> {
        match self {
            Self::Small(n) => Some(*n),
            Self::Big(_) => None,
        }
    }

    pub(super) fn index(&self) -> Option<usize> {
        usize::try_from(self.small()?).ok()
    }

    pub(super) fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) if let Some(n) = a.checked_add(*b) => Self::Small(n),
            _ => Self::big(self.to_big() + other.to_big()),
        }
    }

    /// `self - other`, where `other` is no greater.
    pub(super) fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => Self::Small(a - b),
            _ => Self::big(self.to_big() - other.to_big()),
        }
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) if let Some(n) = a.checked_mul(*b) => Self::Small(n),
            _ => Self::big(self.to_big() * other.to_big()),
        }
    }

    /// `self / other`, where `other` is not zero.
    pub(super) fn div(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => Self::Small(a / b),
            (Self::Small(_), Self::Big(_)) => Self::ZERO,
            _ => Self::big(self.to_big() / other.to_big()),
        }
    }

    /// `self % other`, where `other` is not zero.
    pub(super) fn rem(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => Self::Small(a % b),
            (Self::Small(_), Self::Big(_)) => self.clone(),
            _ => Self::big(self.to_big() % other.to_big()),
        }
    }

    /// A bitwise operation, `small` on two words and `big` otherwise.
    pub(super) fn bits_with(
        &self,
        other: &Self,
        small: fn(u64, u64) -> u64,
        big: fn(&BigUint, &BigUint) -> BigUint,
    ) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => Self::Small(small(*a, *b)),
            _ => Self::big(big(&self.to_big(), &other.to_big())),
        }
    }

    pub(super) fn shl(&self, by: u16) -> Self {
        match self {
            Self::Small(n) if *n == 0 || u32::from(by) < n.leading_zeros() => Self::Small(n << by),
            _ => Self::big(self.to_big() << usize::from(by)),
        }
    }

    pub(super) fn shr(&self, by: u16) -> Self {
        match self {
            Self::Small(n) => Self::Small(n.checked_shr(u32::from(by)).unwrap_or(0)),
            Self::Big(n) => Self::big(&**n >> usize::from(by)),
        }
    }

    /// The low `bits` bits, which is the number modulo two to the `bits`.
    pub(super) fn low(&self, bits: u16) -> Self {
        match self {
            Self::Small(n) if bits >= 64 => Self::Small(*n),
            Self::Small(n) => Self::Small(n & ((1 << bits) - 1)),
            Self::Big(n) => Self::big(&**n % (BigUint::from(1u8) << usize::from(bits))),
        }
    }

    pub(super) fn from_bytes_le(bytes: &[u8]) -> Self {
        if bytes.len() <= 8 {
            let mut word = [0; 8];
            word[..bytes.len()].copy_from_slice(bytes);
            Self::Small(u64::from_le_bytes(word))
        } else {
            Self::big(BigUint::from_bytes_le(bytes))
        }
    }

    pub(super) fn to_bytes_le(&self) -> Vec<u8> {
        match self {
            Self::Small(n) => n.to_le_bytes().to_vec(),
            Self::Big(n) => n.to_bytes_le(),
        }
    }
}

impl From<u64> for Number {
    fn from(n: u64) -> Self {
        Self::Small(n)
    }
}

impl From<u32> for Number {
    fn from(n: u32) -> Self {
        Self::Small(u64::from(n))
    }
}

impl From<u8> for Number {
    fn from(n: u8) -> Self {
        Self::Small(u64::from(n))
    }
}

impl From<usize> for Number {
    fn from(n: usize) -> Self {
        u64::try_from(n).map_or_else(|_| Self::big(BigUint::from(n)), Self::Small)
    }
}

impl From<&BigUint> for Number {
    fn from(n: &BigUint) -> Self {
        Self::big(n.clone())
    }
}
