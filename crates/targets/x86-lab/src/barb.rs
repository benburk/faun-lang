//! The shared Barb input and its test fixtures.
pub(crate) use ::barb::*;

#[cfg(test)]
pub(crate) use ::barb::fixture;
#[cfg(test)]
pub(crate) use ::barb::test_support::{fold, normalize_with_limits, structural};
