"""Count MD5's x86-lab allocator calls with the same I/O at two input sizes.

Build main.fn with --symbols and pass the image to this script. Both inputs
fit in one read and have the same padding. Extra calls at the larger size
would expose an allocation cost in processing the additional full blocks.
"""

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile


def calls(image, size, work):
    # starti loads the standalone position-independent ELF before we resolve
    # its allocator. Each breakpoint hit is counted by GDB without a stop.
    data = bytes(i % 256 for i in range(size))
    (work / "input").write_bytes(data)
    run = subprocess.run(
        [
            "gdb",
            "-nx",
            "-q",
            "-batch",
            "-ex",
            "set disable-randomization off",
            "-ex",
            "starti < input > output",
            "-ex",
            """python bp = gdb.Breakpoint("*'nat.allocate'", internal=True)""",
            "-ex",
            "python bp.ignore_count = 2147483647",
            "-ex",
            "continue",
            "-ex",
            """python print("allocations", bp.hit_count, "exit", int(gdb.parse_and_eval("$_exitcode")))""",
            str(image),
        ],
        cwd=work,
        capture_output=True,
        text=True,
        check=True,
    )
    hit = re.search(r"^allocations (\d+) exit 0$", run.stdout, re.MULTILINE)
    if hit is None:
        raise SystemExit(f"GDB could not count allocations.\n{run.stdout}{run.stderr}")
    expected = hashlib.md5(data).hexdigest().encode() + b"\n"
    if (work / "output").read_bytes() != expected:
        raise SystemExit(f"incorrect digest at {size} bytes")
    return int(hit[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "image", type=Path, help="x86-lab MD5 executable built with --symbols"
    )
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="md5-calls-") as directory:
        work = Path(directory)
        image = args.image.resolve()
        short = calls(image, 64, work)
        long = calls(image, 4096, work)
    print(f"64 bytes: {short} calls, 4096 bytes: {long} calls")
    if long > short:
        raise SystemExit(
            f"{long - short} extra allocator calls over 63 additional blocks"
        )


if __name__ == "__main__":
    main()
