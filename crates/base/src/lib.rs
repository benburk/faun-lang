//! What every tier of the Faun compiler says alike, said once beneath them
//! all: Barb, machine IR and each target read these and none owns them.
//!
//! - [`index`]: dense indices into flat arrays, and runs within them, the
//!   way every tier keeps a program
//! - [`float`]: the IEEE 754 operations and formats a tier may compute or
//!   hand on
//! - [`facts`]: what is known about a number, which Barb works out, machine
//!   IR holds a value at, and a target sizes it by

pub mod facts;
pub mod float;
pub mod index;
