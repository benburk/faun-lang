//! The machine IR. Names no register, syscall, instruction set, or word
//! width until representation is legalized. Programs containing target-sized
//! data then record a checked [`Layout`] obligation.
//!
//! It decides:
//!
//! - Representation: the form each value takes, and the width it needs
//! - Ownership: where a value is retained and released, and when storage is
//!   unique enough to be reused in place
//! - Layout: what is data, what is global, and what an offset means
//! - Function signatures: arity, and the class of each parameter and result
//!
//! Defined and external functions share IDs and [`Op::Call`]. Signatures
//! describe classes and [`Returns`]; bodies alone own parameter values.
//! External declarations are not a provider catalog: targets check symbol
//! availability and ABI before emitting calls.
//!
//! It does not decide:
//!
//! - Which values live in registers and which in memory
//! - Calling conventions, stacks, and frames
//! - Instruction selection and encoding
//! - The target's word size, and what its platform provides
//!
//! Instructions live in one flat array, and everything of variable length --
//! operand lists, the regions a construct holds -- is a range into a pool
//! beside it. Nothing about an instruction is boxed or owned, so replacing
//! one is a store and a pass over them is a linear scan.
//!
//! Control flow is nested and never flattened to blocks and jumps:
//!
//! - Structure lowers to jumps in about fifteen lines. The reverse needs a
//!   Relooper, which emscripten and LLVM's wasm backend each carry.
//! - Regions take parameters, so a loop stays the tail call it was written
//!   as and no target reconstructs one.
//! - A region's instructions are contiguous, so walking one stays sequential
//!   where a graph of blocks would scatter.
//!
//! A word constant is 64 bits of pattern, not a signed number:
//!
//! - `-1` and `u64::MAX` describe the same 64-bit pattern.
//! - Signedness picks `div` against `idiv` and `jb` against `jl`, so it
//!   belongs to operations. LLVM dropped signed and unsigned integer types;
//!   wasm never had them.
//!
//! Unbounded naturals are different: [`Class::Natural`] and
//! [`Op::NaturalConstant`] retain arbitrary precision. A target must either
//! implement that representation or reject it, never select its word size.
//!
//! # Code organization
//!
//! - `model`: operations, regions, declarations, IDs, and their small methods.
//! - `program`: [`Program`], its pools, queries, and construction entry points.
//! - `builder`: [`Builder`], the temporary state for scoped region construction.
//! - Other modules own named algorithms: validation, evaluation, lowering,
//!   and legalization. Ordinary program queries and mutations stay with the
//!   owning type rather than being split into read and write modules.
//!
//! Barb follows the same split. Public types are re-exported here; the file
//! layout is not part of the public API.

mod arithmetic;
#[path = "../../../core/src/ir/bounds.rs"]
mod bounds;
mod builder;
#[path = "../../../core/src/ir/lab/cell.rs"]
mod cell;
mod common;
mod digits;
pub mod evaluate;
mod fit;
mod layout;
#[path = "../../../core/src/ir/lab/legalize.rs"]
mod legalize;
#[path = "../../../core/src/ir/lab/lower.rs"]
mod lower;
mod model;
#[path = "../../../core/src/ir/natural.rs"]
pub mod natural;
mod optimize;
#[path = "../../../core/src/ir/lab/ownership.rs"]
mod ownership;
#[path = "../../../core/src/ir/packing.rs"]
mod packing;
mod pretty;
mod program;
mod prune;
#[path = "../../../core/src/ir/lab/region.rs"]
mod region;
mod rewrite;
mod rotate;
#[path = "../../../core/src/ir/lab/sequence.rs"]
mod sequence;
mod shifts;
mod simplify;
mod split;
mod uniqueness;
mod validate;
#[path = "../../../core/src/ir/lab/word_comparisons.rs"]
pub(crate) mod word_comparisons;

pub use bounds::conversions_taking_nothing;
pub use builder::Builder;
pub use fit::{Budget, fit};
pub use layout::Layout;
pub use legalize::legalize;
pub use lower::{MAKE_ARGUMENTS, lower, lower_counting_arguments};
pub use model::{
    Binary, Class, DataId, Definition, Direction, Exit, Function, FunctionId, Offset, Op, Origin,
    Range, Region, RegionId, Relation, Returns, ShapeId, Span, Terminator, ValueId, Width,
};
pub use optimize::optimize;
pub use program::Program;
pub use rotate::rotate;
pub use shifts::expand_shifts;
pub use split::split;
pub use validate::validate;

#[cfg(test)]
mod arithmetic_tests;
#[cfg(test)]
mod bounds_tests;
#[cfg(test)]
mod common_tests;
#[cfg(test)]
mod cost_tests;
#[cfg(test)]
mod external_tests;
#[cfg(test)]
mod fit_tests;
#[cfg(test)]
mod flow_tests;
#[cfg(test)]
mod interpreter_tests;
#[cfg(test)]
mod legalize_tests;
#[cfg(test)]
mod natural_tests;
#[cfg(test)]
mod optimize_tests;
#[cfg(test)]
mod ownership_tests;
#[cfg(test)]
mod representation_tests;
#[cfg(test)]
mod split_tests;
#[cfg(test)]
mod test_support;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod validation_tests;
#[cfg(test)]
mod zero_width_tests;
