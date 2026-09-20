//! Shared folding policy for evaluation and bounded traversal of constants.

use std::fmt;

/// Resource limits for one whole folding pass, not language integer limits.
/// Work counts visits, copied bytes and conservative bigint word operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldLimits {
    pub work: u64,
    pub max_bytes: usize,
    pub max_depth: usize,
}

impl Default for FoldLimits {
    fn default() -> Self {
        Self {
            work: 1_000_000,
            max_bytes: 8192,
            max_depth: 128,
        }
    }
}

/// Why a bounded operation stopped. Refusal is not an invalid constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitExceeded {
    Work,
    Depth,
    ValueSize,
}

impl fmt::Display for LimitExceeded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "constant evaluation limit exceeded: {self:?}")
    }
}
impl std::error::Error for LimitExceeded {}

#[derive(Debug)]
pub struct Budget {
    pub(super) remaining: u64,
    limits: FoldLimits,
    depth: usize,
}

impl Budget {
    #[must_use]
    pub const fn new(limits: FoldLimits) -> Self {
        Self {
            remaining: limits.work,
            limits,
            depth: 0,
        }
    }

    pub(super) const fn spend(&mut self, work: u64) -> Result<(), LimitExceeded> {
        if work > self.remaining {
            self.remaining = 0;
            return Err(LimitExceeded::Work);
        }
        self.remaining -= work;
        Ok(())
    }

    pub(super) fn bytes(&mut self, size: usize) -> Result<(), LimitExceeded> {
        if size > self.limits.max_bytes {
            return Err(LimitExceeded::ValueSize);
        }
        self.spend(u64::try_from(size).map_err(|_| LimitExceeded::ValueSize)?)
    }

    /// Expression visits and encoded-field scans share the same depth limit.
    /// Restore depth even when a nested operation declines to evaluate.
    pub(super) fn descend<T, E: From<LimitExceeded>>(
        &mut self,
        visit: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        self.spend(1)?;
        if self.depth >= self.limits.max_depth {
            return Err(LimitExceeded::Depth.into());
        }
        self.depth += 1;
        let result = visit(self);
        self.depth -= 1;
        result
    }
}
