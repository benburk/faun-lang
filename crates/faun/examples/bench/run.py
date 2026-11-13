#!/usr/bin/env python3
"""Time a set of Faun programs, built by one compiler or several, on fixed
inputs: JSON parsing and decoding, grep, word frequency, hex encoding, a SAT search,
n-body and spectral norm. Every build's answer must agree with the first
compiler's before any is timed. Runs alternate, pinned to one CPU, and the
median time, peak RSS, and executable size are reported. Where available,
`perf stat` counts instructions in a separate run.

    python3 run.py --cpu 3
    python3 run.py --cpu 3 --faun old=/tmp/old/faun --faun new=target/release/faun

Instructions are the steadier measure: they move little with the machine's
load, so a change to the compiler shows in them where times are noisy."""

import argparse
from collections import Counter
import os
from pathlib import Path
import random
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
EXAMPLES = HERE.parent
REPOSITORY = EXAMPLES.parent.parent.parent

# Each benchmark: its source, its arguments, and the input it reads.
BENCHMARKS = [
    ("json-parse", EXAMPLES / "libraries/json/bench/parse.fn", [], "users.json"),
    ("json-decode", EXAMPLES / "libraries/json/bench/decode.fn", [], "users.json"),
    ("grep", HERE / "grep.fn", [".*(error|warn).*timeout.*"], "log.txt"),
    ("hex-encode", HERE / "hex-encode.fn", [], "binary.dat"),
    ("wordfreq", HERE / "wordfreq.fn", [], "words.txt"),
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
    words = directory / "words.txt"
    chapter = (REPOSITORY / "crates/faun/standard/README.md").read_bytes()
    words.write_bytes((chapter + b"\n") * 16)
    binary = directory / "binary.dat"
    binary.write_bytes(random.Random(19).randbytes(256 * 1024))
    return {
        "users.json": users,
        "log.txt": log,
        "words.txt": words,
        "binary.dat": binary,
    }


def word_counts(path):
    """An independent concordance of the complete input."""
    stop = set(
        b"a an and are as at be by for from in is it of on or that the this to with".split()
    )
    counts = Counter(
        word
        for word in re.findall(rb"[a-z]+", path.read_bytes().lower())
        if word not in stop
    )
    return b"".join(
        word + b"\t" + str(n).encode() + b"\n" for word, n in sorted(counts.items())
    )


def execute(command, stdin_path):
    with (stdin_path or Path(os.devnull)).open("rb") as stdin:
        return subprocess.run(command, stdin=stdin, capture_output=True, check=True)


def instructions(command, stdin_path, perf, expected):
    result = execute(
        [perf, "stat", "-x,", "-e", "instructions:u", "--", *command], stdin_path
    )
    if result.stdout != expected:
        raise SystemExit(f"{command[0]}: output changed during instruction counting")
    for line in result.stderr.decode().splitlines():
        fields = line.split(",")
        if len(fields) > 2 and "instructions" in fields[2] and fields[0].isdigit():
            return int(fields[0])
    return None


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
    parser.add_argument("--backend", help="Faun backend passed to every compiler")
    parser.add_argument(
        "--only", default="", help="run only benchmarks whose names hold this"
    )
    args = parser.parse_args()
    if args.runs < 1:
        parser.error("--runs must be positive")
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside this process's allowed affinity")
    os.sched_setaffinity(0, {args.cpu})
    compilers = []
    backend = [f"--backend={args.backend}"] if args.backend else []
    for given in args.faun or [f"faun={REPOSITORY / 'target/release/faun'}"]:
        label, _, path = given.partition("=")
        compilers.append((label, path or label))
    with tempfile.TemporaryDirectory(prefix="faun-bench-") as directory:
        work = Path(directory)
        probe = work / "measure"
        metrics = work / "metrics"
        subprocess.run(
            [
                os.environ.get("CC", "cc"),
                "-O2",
                EXAMPLES / "benchmarks-game/measure.c",
                "-o",
                probe,
            ],
            check=True,
        )
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
                    [
                        compiler,
                        "build",
                        *backend,
                        str(source),
                        "-o",
                        str(image),
                    ],
                    check=True,
                    stdout=subprocess.DEVNULL,
                )
                builds.append((label, image))
            expected = None
            if name == "wordfreq":
                expected = word_counts(stdin_path)
            elif name == "hex-encode":
                expected = stdin_path.read_bytes().hex().encode("ascii") + b"\n"
            for label, image in builds:
                answer = execute([image, *arguments], stdin_path).stdout
                if expected is None:
                    expected = answer
                elif answer != expected:
                    raise SystemExit(
                        f"{name}: {label} answered {answer!r}, not {expected!r}"
                    )
            times = {label: [] for label, _ in builds}
            memory = {label: [] for label, _ in builds}
            counts = {label: [] for label, _ in builds}
            for trial in range(args.runs):
                for label, image in builds[:: 1 if trial % 2 == 0 else -1]:
                    command = [str(image), *arguments]
                    result = execute([probe, "0", metrics, *command], stdin_path)
                    if result.stdout != expected:
                        raise SystemExit(
                            f"{name}: {label} output changed during timing"
                        )
                    ns, rss = map(int, metrics.read_text().split())
                    times[label].append(ns / 1e9)
                    memory[label].append(rss)
                    if args.perf:
                        count = instructions(command, stdin_path, args.perf, expected)
                        if count is not None:
                            counts[label].append(count)
            for label, image in builds:
                count = statistics.median(counts[label]) if counts[label] else None
                rows.append(
                    (
                        name,
                        label,
                        statistics.median(times[label]),
                        count,
                        statistics.median(memory[label]),
                        image.stat().st_size,
                    )
                )
    baseline = {}
    print(
        f"{'benchmark':14} {'compiler':10} {'time':>10} {'instructions':>16} {'peak RSS':>11} {'ELF bytes':>10}"
    )
    for name, label, seconds, count, rss, size in rows:
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
            f"{name:14} {label:10} {seconds * 1000:8.1f} ms {shown:>16} {rss:7,.0f} KiB {size:10,}{ratio}"
        )


if __name__ == "__main__":
    main()
