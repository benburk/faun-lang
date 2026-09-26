//! MOS 6502 under cc65's sim65.
//!
//! A word is sixteen bits, the width of an address, and the registers are
//! eight, so every word operation is two byte operations with a carry.
//! Values live in a frame on a software stack, reached through a zero-page
//! pointer; the hardware stack carries only return addresses, which bounds
//! recursion at 128 deep until those move too.
//!
//! The image is a twelve-byte header, the data, and the code, loaded at
//! `$0200`. The platform is the simulator's hooks, and `grow` is a bump
//! upwards from the end of the image toward the stack.

#[cfg(test)]
mod abi_tests;
mod asm;
mod image;
mod lower;
#[cfg(test)]
mod tests;

use std::io;
use std::path::{Path, PathBuf};

use faun_core::ir::{Budget, Op, Program, RegionId};
use faun_core::targets::{Target, write_image};

/// Where sim65 loads the image, and the zero-page pairs below it.
const LOAD: u16 = 0x0200;

/// The C stack the simulator's hooks take their arguments on. Its address
/// goes in the header, and nothing else uses it.
const CSP: u8 = 0x02;
const CSTACK_TOP: u16 = 0xFE00;

/// The frame pointer, and the stack of frames it walks down.
const FP: u8 = 0x04;
const FRAMES_TOP: u16 = 0xFD00;

/// Scratch pairs: every two-operand form works through these.
const T0: u8 = 0x06;
const T1: u8 = 0x08;
/// The pair an indirect load or store reaches its address through.
const PTR: u8 = 0x0A;
/// Where a function leaves its result, and where a caller puts arguments.
const R0: u8 = 0x0C;
const ARGS: u8 = 0x0E;
const ARG_COUNT: u8 = 4;
/// The bump allocator's cursor, set at reset to the end of the image.
const HEAP: u8 = 0x16;
/// Zero-page pairs a function may keep its most used values in, rather than
/// reaching them through `FP`. Each costs the function saving and restoring
/// it around calls, so the count is modest.
const HOMES: u8 = 0x18;
const HOME_COUNT: u8 = 16;

/// Where the count of arguments is kept, read once at reset.
const ARGC: u8 = HOMES + 2 * HOME_COUNT;

/// The simulator's hooks: a `jmp` or `jsr` to one is answered by the host.
const HOOK_OPEN: u16 = 0xFFF4;
const HOOK_CLOSE: u16 = 0xFFF5;
const HOOK_READ: u16 = 0xFFF6;
const HOOK_WRITE: u16 = 0xFFF7;
const HOOK_ARGS: u16 = 0xFFF8;
const HOOK_EXIT: u16 = 0xFFF9;

/// How wide this machine's own word is, which is the widest value it holds
/// and what any class but a fixed one means here.
pub(crate) const WORD_BITS: u16 = 16;

/// This target, for whoever is choosing between them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mos6502Sim65;

impl Target for Mos6502Sim65 {
    fn name(&self) -> &'static str {
        "mos6502-sim65"
    }

    fn word(&self) -> u16 {
        WORD_BITS
    }

    fn provides(&self) -> &'static [&'static str] {
        &[
            "fd_put!",
            "fd_take!",
            "fd_taken!",
            "fd_open!",
            "fd_close!",
            "exit!",
            "write_fd!",
            "read_fd!",
            "open_at!",
            "write!",
            "read_byte!",
            "grow",
            "argc",
            "argv",
        ]
    }

    fn budget(&self) -> Budget {
        Budget::new(usize::from(ARG_COUNT), 1, TRANSFER_COUNT)
    }

    fn limits(&self, program: &Program) -> Result<(), String> {
        let entry = program.entry();
        // Each entry parameter is a startup value: the count, then where the
        // arguments' addresses lie.
        for (at, name) in program.parameter_names(entry).enumerate() {
            if ![(0, "argc"), (1, "argv")].contains(&(at, name)) {
                return Err(format!(
                    "mos6502-sim65 cannot supply entry parameter {at} `{name}`"
                ));
            }
        }
        for function in program.functions() {
            let name = program.name(function.name);
            if function.params.len() > usize::from(ARG_COUNT) {
                return Err(format!(
                    "mos6502-sim65 function `{name}` has {} parameters; at most {ARG_COUNT} are supported",
                    function.params.len()
                ));
            }
            if function.returns.classes().len() > 1 {
                return Err(format!(
                    "mos6502-sim65 function `{name}` has {} results; at most 1 is supported",
                    function.returns.classes().len()
                ));
            }
            if let Some(body) = function.body() {
                region_limits(program, name, body)?;
            }
        }
        lower::check_frames(program)
    }

    fn emit(&self, program: &Program) -> Vec<u8> {
        image::image(&lower::lower(program), program)
    }

    /// An image named `output.bin`, for `sim65` to run.
    fn write(&self, image: &[u8], output: &Path) -> io::Result<PathBuf> {
        write_image(output, ".bin", image, false)
    }
}

/// Values a region edge carries: one per scratch pair.
const TRANSFER_COUNT: usize = 2;

/// All nested region edges use at most the two scratch pairs. Function
/// parameters arrive in separate argument pairs and are checked separately.
fn region_limits(program: &Program, name: &str, body: RegionId) -> Result<(), String> {
    let mut regions = vec![body];
    while let Some(region) = regions.pop() {
        for (op, results) in program.walk(region) {
            let (kind, count) = match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    regions.extend([then_region, else_region]);
                    ("if results", results.len())
                }
                Op::Loop { initial, body } => {
                    regions.push(body);
                    if initial.len() > TRANSFER_COUNT {
                        return Err(format!(
                            "mos6502-sim65 function `{name}` region {} has {} loop parameters; at most {TRANSFER_COUNT} are supported",
                            region.index(),
                            initial.len()
                        ));
                    }
                    ("loop results", results.len())
                }
                _ => continue,
            };
            if count > TRANSFER_COUNT {
                return Err(format!(
                    "mos6502-sim65 function `{name}` region {} has {count} {kind}; at most {TRANSFER_COUNT} are supported",
                    region.index()
                ));
            }
        }
    }
    Ok(())
}

struct Code {
    bytes: Vec<u8>,
    /// Where the code begins, which is after the data, and so where the
    /// machine has to be started.
    reset: u16,
    /// Whether anything in it pushes onto the hardware stack.
    pushes: bool,
}
