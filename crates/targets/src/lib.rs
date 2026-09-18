//! Which targets this compiler was built with.
//!
//! A target is a crate implementing [`faun::targets::Target`], so the set of
//! them is a fact about a build rather than about the compiler: adding one
//! is a dependency and a line here, and nothing below this knows how many
//! there are. What is here is only the choosing -- by name for whoever asked
//! for one, and all of them for whatever wants every answer.

use faun::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

/// Every target there is here, in the order they were written.
pub const ALL: [&dyn Target; 3] = [&X86_64Linux, &Wasm32Wasi, &Mos6502Sim65];

/// The target native to the machine the compiler is running on, if there is
/// one here for it. `None` means `--target` is not optional on this machine.
pub const HOST: Option<&dyn Target> = if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
    Some(&X86_64Linux)
} else {
    None
};

/// The one that answers to `name`.
#[must_use]
pub fn from_name(name: &str) -> Option<&'static dyn Target> {
    ALL.into_iter().find(|target| target.name() == name)
}

/// What each is called, for saying what there was to choose from.
#[must_use]
pub fn names() -> Vec<&'static str> {
    ALL.iter().map(|target| target.name()).collect()
}
