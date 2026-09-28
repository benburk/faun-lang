//! Pieces of code generation a target may take up, each a small library.
//!
//! What a machine with a file of registers shares with others like it is
//! kept here, so a new target of that kind brings a description of itself
//! rather than an allocator.
//!
//! - [`registers`]: register allocation over a target's instructions, each
//!   saying which registers its operands must or may be in.
//! - [`parallel_copy`]: moving several values between places at once, as
//!   the edges and operands an allocation leaves need.
//!
//! A target reached through something else -- a stack machine, or one whose
//! values live in memory -- takes none of this.

pub mod parallel_copy;
pub mod registers;

/// A register of a target's file, which it names as it likes and numbers
/// below 64 for sets of them.
pub trait Register: Copy + Eq + core::fmt::Debug {
    fn number(self) -> u8;
}

/// A set of registers, by number.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RegSet(pub u64);

impl RegSet {
    pub const EMPTY: Self = Self(0);

    #[must_use]
    pub fn of<R: Register>(regs: &[R]) -> Self {
        Self(regs.iter().fold(0, |bits, reg| bits | (1 << reg.number())))
    }

    #[must_use]
    pub fn contains<R: Register>(self, reg: R) -> bool {
        self.0 & (1 << reg.number()) != 0
    }

    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

/// A slot of a function's frame, numbered from nought; a target says how
/// far from where the frame is kept each lies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameSlot(u32);

impl FrameSlot {
    #[must_use]
    pub const fn at(index: u32) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn number(self) -> u32 {
        self.0
    }
}
