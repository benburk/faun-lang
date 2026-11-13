//! Portable lab representations over the same machine IR the target emits.
use super::{
    Binary, Builder, Class, DataId, Exit, Function, FunctionId, Offset, Op, Origin, Program, Range,
    RegionId, Relation, Returns, ShapeId, Terminator, ValueId, Width, arithmetic, bounds, model,
    natural, packing, program, prune, rewrite, uniqueness, validate,
};
mod cell;
mod legalize;
mod lower;
mod ownership;
mod region;
mod sequence;
mod word_comparisons;
pub use legalize::legalize;
pub use lower::{MAKE_ARGUMENTS, lower, lower_counting_arguments};
pub(crate) use word_comparisons::lower as lower_word_comparisons;
