//! The shared planner of simultaneous moves, over this target's registers.

use super::machine::Reg;

pub(crate) use faun_core::codegen::parallel_copy::{CopySource, plan, temporary};

pub(crate) type Place = faun_core::codegen::parallel_copy::Place<Reg>;
pub(crate) type Copy = faun_core::codegen::parallel_copy::Copy<Reg>;
pub(crate) type Move = faun_core::codegen::parallel_copy::Move<Reg>;
