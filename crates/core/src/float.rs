//! IEEE 754 arithmetic on bit patterns, said once for every tier that reads
//! it.
//!
//! A float here is its bit pattern, a number of 32 or 64 bits, and never a
//! value of its own kind: Barb holds the pattern in whatever the frontend
//! wrapped it in, machine IR holds it as a number of that many bits, and a
//! target moves it into a float register only for the instruction. What
//! these operations answer is the one IEEE 754-2019 specifies under
//! round-to-nearest-even and default exception handling, which is what the
//! host's own `f32` and `f64` compute, and what SSE2 computes with its
//! control word as a process starts. A NaN's sign and payload are left to
//! whoever computes it: a program sees every NaN as one value, so nothing
//! may depend on which pattern one arrives as.

/// Which IEEE 754 format: how many bits a pattern takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Format {
    Binary32,
    Binary64,
}

impl Format {
    #[must_use]
    pub const fn bits(self) -> u16 {
        match self {
            Self::Binary32 => 32,
            Self::Binary64 => 64,
        }
    }

    /// The greatest pattern of the format.
    #[must_use]
    pub const fn greatest(self) -> u64 {
        match self {
            Self::Binary32 => 0xFFFF_FFFF,
            Self::Binary64 => u64::MAX,
        }
    }
}

/// An operation every IEEE 754 format has, correctly rounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Sqrt,
}

impl Operation {
    /// How many patterns it takes.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::Sqrt => 1,
            Self::Add | Self::Sub | Self::Mul | Self::Div => 2,
        }
    }
}

/// One operation at one format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Float {
    pub operation: Operation,
    pub format: Format,
}

impl Float {
    /// The pattern it answers for these, each taken as a pattern of the
    /// format: bits above the format's are not part of one.
    ///
    /// # Panics
    ///
    /// If it is handed other than [`Operation::arity`] patterns.
    #[must_use]
    pub fn calculate(self, patterns: &[u64]) -> u64 {
        assert_eq!(patterns.len(), self.operation.arity(), "a float's operands");
        match self.format {
            Format::Binary64 => {
                let a = f64::from_bits(patterns[0]);
                let b = patterns.get(1).copied().map_or(0.0, f64::from_bits);
                match self.operation {
                    Operation::Add => a + b,
                    Operation::Sub => a - b,
                    Operation::Mul => a * b,
                    Operation::Div => a / b,
                    Operation::Sqrt => a.sqrt(),
                }
                .to_bits()
            }
            Format::Binary32 => {
                let narrow = |pattern: u64| {
                    f32::from_bits(u32::try_from(pattern & 0xFFFF_FFFF).expect("32 bits"))
                };
                let a = narrow(patterns[0]);
                let b = patterns.get(1).copied().map_or(0.0, narrow);
                u64::from(
                    match self.operation {
                        Operation::Add => a + b,
                        Operation::Sub => a - b,
                        Operation::Mul => a * b,
                        Operation::Div => a / b,
                        Operation::Sqrt => a.sqrt(),
                    }
                    .to_bits(),
                )
            }
        }
    }
}

impl std::fmt::Display for Float {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let format = match self.format {
            Format::Binary32 => "binary32",
            Format::Binary64 => "binary64",
        };
        let operation = match self.operation {
            Operation::Add => "add",
            Operation::Sub => "sub",
            Operation::Mul => "mul",
            Operation::Div => "div",
            Operation::Sqrt => "sqrt",
        };
        write!(f, "{format} {operation}")
    }
}

#[cfg(test)]
mod tests {
    use super::{Float, Format, Operation};

    #[test]
    fn a_pattern_is_answered_as_the_host_rounds_it() {
        let add = Float {
            operation: Operation::Add,
            format: Format::Binary64,
        };
        assert_eq!(
            add.calculate(&[0.1f64.to_bits(), 0.2f64.to_bits()]),
            0.300_000_000_000_000_04f64.to_bits()
        );
        let sqrt = Float {
            operation: Operation::Sqrt,
            format: Format::Binary32,
        };
        assert_eq!(sqrt.calculate(&[2.0f32.to_bits().into()]), 0x3fb5_04f3);
        // Bits above a binary32 pattern are not part of it.
        assert_eq!(
            sqrt.calculate(&[(1 << 40) | u64::from(4.0f32.to_bits())]),
            u64::from(2.0f32.to_bits())
        );
    }
}
