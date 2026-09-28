#!/usr/bin/env python3
"""Check printed energies, then alternate pinned runs of prebuilt executables."""

import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import time


def energies(program, steps):
    output = subprocess.check_output([str(program), str(steps)])
    if output.startswith(b"Ok(") and output.endswith(b")\n"):
        output = output[3:-2] + b"\n"
    if len(output.splitlines()) != 2:
        raise SystemExit(f"{program}: expected two energy lines, got {output!r}")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cpu", type=int, required=True, help="an allowed, idle Linux CPU"
    )
    parser.add_argument("--steps", type=int, default=1_000_000)
    parser.add_argument("--runs", type=int, default=7)
    parser.add_argument("programs", type=Path, nargs="+")
    args = parser.parse_args()
    if args.steps < 0 or args.runs < 1:
        parser.error("steps must be nonnegative and runs must be positive")
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside this process's allowed affinity")
    programs = [path.resolve(strict=True) for path in args.programs]
    if len(set(programs)) != len(programs):
        parser.error("pass each executable only once")
    os.sched_setaffinity(0, {args.cpu})

    # The chosen timing count is checked last, warming every executable.
    counts = [n for n in [0, 1, 10, 1000, 10000, 100000, 1000000] if n != args.steps]
    counts.append(args.steps)
    expected = None
    for count in counts:
        expected = energies(programs[0], count)
        for program in programs[1:]:
            actual = energies(program, count)
            if actual != expected:
                raise SystemExit(f"{program} at {count}: {actual!r} != {expected!r}")
    samples = {str(program): [] for program in programs}
    for trial in range(args.runs):
        for program in programs[:: 1 if trial % 2 == 0 else -1]:
            start = time.perf_counter()
            actual = energies(program, args.steps)
            samples[str(program)].append(time.perf_counter() - start)
            if actual != expected:
                raise SystemExit(f"{program}: timed energy mismatch")
    print(
        json.dumps(
            {
                "cpu": args.cpu,
                "steps": args.steps,
                "verified_steps": counts,
                "energies": expected.decode("ascii").splitlines(),
                "programs": {
                    program: {
                        "median_seconds": statistics.median(times),
                        "seconds": times,
                    }
                    for program, times in samples.items()
                },
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
