"""Run a WASI module and print what it took: its exit status, the fuel it
burned, the bytes of linear memory it touched, and the nanoseconds `_start`
ran for.

    wasm.py MODULE STDIN STDOUT FUEL [ARGUMENT...]

Fuel counts the WebAssembly instructions run, the same every time. Memory
is the linear memory's pages the module read or wrote, counted where the
kernel says which are there: a module's memory grows a 64 KiB page at a
time, far coarser than what it uses, and never shrinks, so what is touched
at the end is the peak. A module that runs out of fuel is stopped and
answers 124, as `timeout` does.
"""

import ctypes
import os
import struct
import sys
import time

from wasmtime import Config, Engine, ExitTrap, Linker, Module, Store, Trap, WasiConfig


def touched(start, length):
    """The bytes of a mapping in pages that are present: `/proc/self/pagemap`
    holds a word for each page, its top bit set where the page is there."""
    page = os.sysconf("SC_PAGE_SIZE")
    first = ctypes.cast(start, ctypes.c_void_p).value // page
    with open("/proc/self/pagemap", "rb") as pagemap:
        pagemap.seek(first * 8)
        words = pagemap.read(-(-length // page) * 8)
    return page * sum(word >> 63 for (word,) in struct.iter_unpack("<Q", words))


def main():
    # Huge pages would count two megabytes for a touched byte.
    ctypes.CDLL(None).prctl(41, 1, 0, 0, 0)
    module, stdin, stdout, fuel, *arguments = sys.argv[1:]
    config = Config()
    config.consume_fuel = True
    engine = Engine(config)
    store = Store(engine)
    wasi = WasiConfig()
    wasi.argv = [module, *arguments]
    wasi.stdin_file = stdin
    wasi.stdout_file = stdout
    wasi.inherit_stderr()
    store.set_wasi(wasi)
    store.set_fuel(int(fuel))
    linker = Linker(engine)
    linker.define_wasi()
    instance = linker.instantiate(store, Module.from_file(engine, module))
    exports = instance.exports(store)
    status = 0
    start = time.perf_counter_ns()
    try:
        exports["_start"](store)
    except ExitTrap as exit:
        status = exit.code
    except Trap as trap:
        print(trap.message, file=sys.stderr)
        status = 124 if store.get_fuel() == 0 else 134
    elapsed = time.perf_counter_ns() - start
    memory = exports.get("memory")
    held = touched(memory.data_ptr(store), memory.data_len(store)) if memory else 0
    print(status, int(fuel) - store.get_fuel(), held, elapsed)


if __name__ == "__main__":
    main()
