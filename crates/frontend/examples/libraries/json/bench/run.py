#!/usr/bin/env python3
"""Time the JSON library against Rust's serde_json, Node and Python on the
same input: `parse` reads a tree and walks all of it, `decode` reads typed
records and writes them back. Every program's answer must agree before any
is timed; runs alternate, pinned to one CPU, and the median is reported
with the largest resident size.

    python3 run.py --cpu 3 --count 20000

Needs `faun` (or `--faun`), `cargo` with serde and serde_json available,
`node` and `python3`. With `--wasm`, also the Faun programs under wasmtime."""

import argparse
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
BENCHMARKS = ["parse", "decode"]


def run(command, stdin_path):
    """The program's output, seconds and largest resident size in KiB."""
    with open(stdin_path, "rb") as stdin:
        start = time.perf_counter()
        child = subprocess.Popen(command, stdin=stdin, stdout=subprocess.PIPE)
        output = child.stdout.read()
        _, status, usage = os.wait4(child.pid, 0)
        elapsed = time.perf_counter() - start
    if os.waitstatus_to_exitcode(status) != 0:
        raise SystemExit(f"{command[0]} failed with status {status}")
    return output, elapsed, usage.ru_maxrss


def build(faun, rust_target, wasm, work):
    """Each benchmark's programs, by name, as commands."""
    subprocess.run(
        [
            "cargo",
            "build",
            "--release",
            "--offline",
            "--quiet",
            "--manifest-path",
            str(HERE / "reference" / "rust" / "Cargo.toml"),
            "--target-dir",
            str(rust_target),
        ],
        check=True,
    )
    programs = {}
    for benchmark in BENCHMARKS:
        source = HERE / f"{benchmark}.fn"
        native = work / benchmark
        subprocess.run(
            [faun, "build", str(source), "-o", str(native)],
            check=True,
            stdout=subprocess.DEVNULL,
        )
        commands = {"faun x86-64": [str(native)]}
        if wasm:
            module = work / f"{benchmark}-wasm"
            subprocess.run(
                [faun, "build", "--target=wasm32-wasi", str(source), "-o", str(module)],
                check=True,
                stdout=subprocess.DEVNULL,
            )
            commands["faun wasm32"] = ["wasmtime", str(module) + ".wasm"]
        commands["rust serde_json"] = [str(rust_target / "release" / benchmark)]
        commands["node"] = ["node", str(HERE / "reference" / f"{benchmark}.js")]
        commands["python"] = [
            sys.executable,
            str(HERE / "reference" / f"{benchmark}.py"),
        ]
        programs[benchmark] = commands
    return programs


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--cpu", type=int, required=True, help="an allowed, idle Linux CPU"
    )
    parser.add_argument(
        "--count", type=int, default=20000, help="user records in the input"
    )
    parser.add_argument("--runs", type=int, default=7)
    parser.add_argument("--faun", default=shutil.which("faun") or "faun")
    parser.add_argument(
        "--wasm", action="store_true", help="also time the wasm32 builds"
    )
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside this process's allowed affinity")
    os.sched_setaffinity(0, {args.cpu})
    with tempfile.TemporaryDirectory(prefix="faun-json-bench-") as directory:
        work = Path(directory)
        data = work / "users.json"
        with open(data, "wb") as out:
            subprocess.run(
                [sys.executable, str(HERE / "generate.py"), str(args.count)],
                stdout=out,
                check=True,
            )
        programs = build(args.faun, work / "rust", args.wasm, work)
        results = {
            "cpu": args.cpu,
            "count": args.count,
            "bytes": data.stat().st_size,
            "benchmarks": {},
        }
        for benchmark, commands in programs.items():
            # Every answer agrees first, which also warms each program.
            answers = {
                name: run(command, data)[0] for name, command in commands.items()
            }
            expected = next(iter(answers.values()))
            for name, answer in answers.items():
                if answer != expected:
                    raise SystemExit(
                        f"{benchmark}: {name} answered {answer!r}, not {expected!r}"
                    )
            samples = {name: [] for name in commands}
            peaks = {name: 0 for name in commands}
            names = list(commands)
            for trial in range(args.runs):
                for name in names[:: 1 if trial % 2 == 0 else -1]:
                    _, seconds, peak = run(commands[name], data)
                    samples[name].append(seconds)
                    peaks[name] = max(peaks[name], peak)
            results["benchmarks"][benchmark] = {
                "answer": expected.decode().strip(),
                "programs": {
                    name: {
                        "median_seconds": statistics.median(times),
                        "seconds": times,
                        "peak_kib": peaks[name],
                    }
                    for name, times in samples.items()
                },
            }
    print(json.dumps(results, indent=2))
    megabytes = results["bytes"] / 1e6
    print(
        f"\n{args.count} users, {megabytes:.1f} MB, median of {args.runs} on CPU {args.cpu}",
        file=sys.stderr,
    )
    for benchmark, result in results["benchmarks"].items():
        print(f"\n{benchmark}: {result['answer']}", file=sys.stderr)
        for name, program in result["programs"].items():
            seconds = program["median_seconds"]
            print(
                f"  {name:16} {seconds * 1000:8.1f} ms {megabytes / seconds:7.1f} MB/s {program['peak_kib'] / 1024:7.1f} MiB",
                file=sys.stderr,
            )


if __name__ == "__main__":
    main()
