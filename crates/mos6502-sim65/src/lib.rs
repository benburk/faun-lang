//! MOS 6502 under cc65's sim65.
//!
//! A word is sixteen bits, the width of an address, and the registers are
//! eight, so every word operation is two byte operations with a carry.
//! Values live in a frame on a software stack, reached through a zero-page
//! pointer, and a second one 256 bytes on for a frame past what an index
//! register reaches; the hardware stack carries only return addresses,
//! which bounds recursion at 128 deep until those move too. A function in
//! a call cycle checks the stack pointer on the way in, and a call that
//! would go deeper says `stack overflow` on standard error and exits with
//! status 3. Where calls cannot go round, how deep they go is known before
//! the program runs, and one whose calls would go deeper, or whose frames
//! would reach the image, is refused rather than built.
//!
//! The image is a twelve-byte header, the data, the globals and the code,
//! loaded at `$0200`. The platform is the simulator's hooks. Memory past the
//! image is the heap's and the frames': `grow` bumps the heap up from the
//! image's end, refusing to pass where the frames have reached, and a
//! function making a frame leaves where it would reach down into the heap:
//! saying `stack overflow` with status 3 in a program whose calls can go
//! round, and otherwise with status 2, as a heap with no more room does.
//! Neither has a size of its own; each has what the other leaves.

#[cfg(test)]
mod abi_tests;
mod asm;
mod calls;
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

/// Where a frame goes on past the 256 bytes `FP` reaches with `Y`: `FP`
/// plus 256, set by a function whose frame is that large on the way in and
/// again after each call, since a callee sets its own.
const FQ: u8 = ARGC + 2;

/// The simulator's hooks: a `jmp` or `jsr` to one is answered by the host.
const HOOK_OPEN: u16 = 0xFFF4;
const HOOK_CLOSE: u16 = 0xFFF5;
const HOOK_READ: u16 = 0xFFF6;
const HOOK_WRITE: u16 = 0xFFF7;
const HOOK_ARGS: u16 = 0xFFF8;
const HOOK_EXIT: u16 = 0xFFF9;

/// How far past the data's start the globals start: past the data, on an
/// even address, where an object in them has one, as a natural's must.
pub(crate) fn globals_offset(program: &Program) -> usize {
    let data = program.data().len();
    // Only globals that may hold a natural's object are placed anywhere in
    // particular.
    if program.globals().is_empty() || !program.has_runtime_naturals() {
        data
    } else {
        data.next_multiple_of(2)
    }
}

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
            "fd_read!",
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
        lower::check_frames(program)?;
        // Only laying the code out says how large it is.
        lower::lower(program).map(|_| ())
    }

    fn emit(&self, program: &Program) -> Vec<u8> {
        let code = lower::lower(program).expect("an accepted program fits the machine");
        image::image(&code, program)
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
