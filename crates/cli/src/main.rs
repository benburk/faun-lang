use std::process::ExitCode;

use faun_driver::Backend;
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

// Parsing constructs many short-lived AST vectors and boxes. Keeping the
// allocator optimized in development builds matters as much as optimizing the
// parser itself; the system allocator made the mixed benchmark about 20% slower.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

const BACKENDS: [Backend; 3] = [
    Backend::standard(
        &X86_64Linux,
        "x86-64-linux",
        cfg!(all(target_arch = "x86_64", target_os = "linux")),
    ),
    Backend::standard(&Wasm32Wasi, "wasm32-wasi", false),
    Backend::standard(&Mos6502Sim65, "mos6502-sim65", false),
];

fn main() -> ExitCode {
    faun_driver::run(&BACKENDS)
}
