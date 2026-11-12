#!/usr/bin/env python3
"""Time a set of Faun programs, built by one compiler or several, on fixed
inputs: JSON parsing and decoding, grep by regex derivatives, a SAT search,
n-body and spectral norm. Every build's answer must agree with the first
compiler's before any is timed. Runs alternate, pinned to one CPU, and the
median time is reported with the instructions `perf stat` counts, where
`perf` is found, and the image's size.

    python3 run.py --cpu 3
    python3 run.py --cpu 3 --faun old=/tmp/old/faun --faun new=target/release/faun

Instructions are the steadier measure: they move little with the machine's
load, so a change to the compiler shows in them where times are noisy."""

import argparse
import os
from pathlib import Path
import random
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
EXAMPLES = HERE.parent
REPOSITORY = EXAMPLES.parent.parent.parent

# Each benchmark: its source, its arguments, and the input it reads.
BENCHMARKS = [
    ("json-parse", EXAMPLES / "libraries/json/bench/parse.fn", [], "users.json"),
    ("json-decode", EXAMPLES / "libraries/json/bench/decode.fn", [], "users.json"),
    ("grep", HERE / "grep.fn", [".*(error|warn).*timeout.*"], "log.txt"),
    ("sat", HERE / "sat.fn", ["7"], None),
    ("nbody", EXAMPLES / "benchmarks-game/n-body/main.fn", ["5000000"], None),
    (
        "spectralnorm",
        EXAMPLES / "benchmarks-game/spectral-norm/main.fn",
        ["2000"],
        None,
    ),
]


def write_log(path, lines):
    """Log lines with a level and a few words, the same text every time."""
    rng = random.Random(7)
    levels = ["info", "debug", "warn", "error"]
    words = "request served user cache miss hit timeout retry db query slow ok connection reset upstream".split()
    with open(path, "w") as out:
        for at in range(lines):
            chosen = " ".join(rng.choice(words) for _ in range(rng.randint(3, 9)))
            out.write(f"{at:06d} {rng.choice(levels)} {chosen}\n")


def inputs(directory):
    """Each input a benchmark reads, by name."""
    users = directory / "users.json"
    with open(users, "wb") as out:
        generator = EXAMPLES / "libraries/json/bench/generate.py"
        subprocess.run(
            [sys.executable, str(generator), "20000"], stdout=out, check=True
        )
    log = directory / "log.txt"
    write_log(log, 30000)
    return {"users.json": users, "log.txt": log}


def measure(command, stdin_path, perf):
    """The program's output, seconds, and instructions where `perf` counts them."""
    stdin = open(stdin_path, "rb") if stdin_path else subprocess.DEVNULL
    try:
        if perf:
            command = [perf, "stat", "-x,", "-e", "instructions:u", "--"] + command
        start = time.perf_counter()
        done = subprocess.run(command, stdin=stdin, capture_output=True, check=True)
        elapsed = time.perf_counter() - start
    finally:
        if stdin_path:
            stdin.close()
    instructions = None
    if perf:
        for line in done.stderr.decode().splitlines():
            fields = line.split(",")
            if len(fields) > 2 and "instructions" in fields[2] and fields[0].isdigit():
                instructions = int(fields[0])
    return done.stdout, elapsed, instructions


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--cpu", type=int, required=True, help="an allowed, idle Linux CPU"
    )
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument(
        "--faun",
        action="append",
        default=[],
        help="LABEL=PATH of a compiler, repeatable; the first is the baseline",
    )
    parser.add_argument(
        "--perf", default=os.environ.get("PERF") or shutil.which("perf")
    )
    parser.add_argument(
        "--only", default="", help="run only benchmarks whose names hold this"
    )
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside this process's allowed affinity")
    os.sched_setaffinity(0, {args.cpu})
    compilers = []
    for given in args.faun or [f"faun={REPOSITORY / 'target/release/faun'}"]:
        label, _, path = given.partition("=")
        compilers.append((label, path or label))
    with tempfile.TemporaryDirectory(prefix="faun-bench-") as directory:
        work = Path(directory)
        files = inputs(work)
        rows = []
        for name, source, arguments, input_name in BENCHMARKS:
            if args.only not in name:
                continue
            stdin_path = files.get(input_name) if input_name else None
            builds = []
            for label, compiler in compilers:
                image = work / f"{name}-{label}"
                subprocess.run(
                    [compiler, "build", str(source), "-o", str(image)],
                    check=True,
                    stdout=subprocess.DEVNULL,
                )
                builds.append((label, image))
            expected = None
            for label, image in builds:
                answer = measure([str(image)] + arguments, stdin_path, None)[0]
                if expected is None:
                    expected = answer
                elif answer != expected:
                    raise SystemExit(
                        f"{name}: {label} answered {answer!r}, not {expected!r}"
                    )
            times = {label: [] for label, _ in builds}
            counts = {label: [] for label, _ in builds}
            for trial in range(args.runs):
                for label, image in builds[:: 1 if trial % 2 == 0 else -1]:
                    _, seconds, instructions = measure(
                        [str(image)] + arguments, stdin_path, args.perf
                    )
                    times[label].append(seconds)
                    if instructions is not None:
                        counts[label].append(instructions)
            for label, image in builds:
                count = statistics.median(counts[label]) if counts[label] else None
                rows.append(
                    (
                        name,
                        label,
                        statistics.median(times[label]),
                        count,
                        image.stat().st_size,
                    )
                )
    baseline = {}
    print(
        f"{'benchmark':14} {'compiler':10} {'time':>10} {'instructions':>16} {'size':>10}"
    )
    for name, label, seconds, count, size in rows:
        base = baseline.setdefault(name, (seconds, count))
        ratio = (
            ""
            if base == (seconds, count)
            else f"  {count / base[1]:.2f}x"
            if count and base[1]
            else ""
        )
        shown = f"{count / 1e6:,.1f} M" if count else "-"
        print(
            f"{name:14} {label:10} {seconds * 1000:8.1f} ms {shown:>16} {size / 1024:8.1f} K{ratio}"
        )


if __name__ == "__main__":
    main()
