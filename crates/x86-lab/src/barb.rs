//! The shared Barb input and its test fixtures.
pub(crate) use faun_core::barb::*;

#[cfg(test)]
pub(crate) use faun_core::barb::test_support::{fold, normalize_with_limits, structural};

#[cfg(test)]
#[path = "../../core/src/barb/fixture.rs"]
pub(crate) mod fixture;
