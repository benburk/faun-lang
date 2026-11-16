#!/usr/bin/env python3
"""Check a benchmark's printed answers agree, then alternate pinned runs of
prebuilt executables. Each executable takes one unsigned argument: n-body's
step count, spectral-norm's size."""

import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import time


def answer(program, argument):
    output = subprocess.check_output([str(program), str(argument)])
    if output.startswith(b"Ok(") and output.endswith(b")\n"):
        output = output[3:-2] + b"\n"
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cpu", type=int, required=True, help="an allowed, idle Linux CPU"
    )
    parser.add_argument(
        "--argument", type=int, required=True, help="the timed argument"
    )
    parser.add_argument(
        "--check",
        default="",
        help="comma-separated arguments whose answers must also agree",
    )
    parser.add_argument("--runs", type=int, default=7)
    parser.add_argument("programs", type=Path, nargs="+")
    args = parser.parse_args()
    if args.argument < 0 or args.runs < 1:
        parser.error("argument must be nonnegative and runs must be positive")
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside this process's allowed affinity")
    programs = [path.resolve(strict=True) for path in args.programs]
    if len(set(programs)) != len(programs):
        parser.error("pass each executable only once")
    os.sched_setaffinity(0, {args.cpu})

    # The timed argument is checked last, warming every executable.
    counts = [int(n) for n in args.check.split(",") if n]
    counts = [n for n in counts if n != args.argument]
    counts.append(args.argument)
    expected = None
    for count in counts:
        expected = answer(programs[0], count)
        for program in programs[1:]:
            actual = answer(program, count)
            if actual != expected:
                raise SystemExit(f"{program} at {count}: {actual!r} != {expected!r}")
    samples = {str(program): [] for program in programs}
    for trial in range(args.runs):
        for program in programs[:: 1 if trial % 2 == 0 else -1]:
            start = time.perf_counter()
            actual = answer(program, args.argument)
            samples[str(program)].append(time.perf_counter() - start)
            if actual != expected:
                raise SystemExit(f"{program}: timed answer mismatch")
    print(
        json.dumps(
            {
                "cpu": args.cpu,
                "argument": args.argument,
                "verified": counts,
                "answer": expected.decode("ascii").splitlines(),
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
