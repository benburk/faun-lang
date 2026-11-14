"""Score Faun's benchmarks-game programs against the game's C programs, as
the game scores them: elapsed time, peak memory and compressed source size.

Each Faun program is first held to the game's own output at a small size,
and at the measured size its output must be the C program's, byte for byte.
Each program is then run `--runs` times, alternating with the other, and
scored by its lowest elapsed time and peak resident memory in a separate run. A
source is scored as the game scores it: comments removed, runs of white
space made one space, and the rest compressed by gzip at its lowest level.

The sizes default to ones a run of the whole set takes a minute or so for;
`--game` asks for the game's own, where some programs take minutes and
k-nucleotide gigabytes.

    python3 run.py
    python3 run.py --only fasta --runs 5 --cpu 3
    python3 run.py --faun target/release/faun --game
"""

import argparse
import gzip
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parent.parent.parent.parent

# Each benchmark: its folder, the size the game checks it at, the size the
# game measures it at, and a smaller size measured by default. k-nucleotide
# reads what fasta writes at its size.
BENCHMARKS = [
    ("binary-trees", 10, 21, 18),
    ("fannkuch-redux", 7, 12, 10),
    ("fasta", 1000, 25000000, 2500000),
    ("k-nucleotide", 1000, 25000000, 250000),
    ("mandelbrot", 200, 16000, 4000),
    ("n-body", 1000, 50000000, 5000000),
    ("pidigits", 27, 10000, 4000),
    ("spectral-norm", 100, 5500, 2000),
]

# One flag set for every C program: the game's own vary a little by program,
# and name the game's machine where these name none.
C_FLAGS = ["-O3", "-fomit-frame-pointer"]
C_LIBRARIES = {"pidigits": ["-lgmp"], "k-nucleotide": [f"-I{HERE / 'k-nucleotide'}"]}


def stripped(source, language):
    """`source` with its comments removed and each run of white space one
    space, as the game measures it."""
    if language == "c":
        source = re.sub(r"/\*.*?\*/", " ", source, flags=re.S)
        source = re.sub(r"//[^\n]*", " ", source)
    else:
        # Rewrites may use '#' as data. Skip comments only in code, including
        # code inside an interpolated string. Braces there can nest.
        kept, contexts = [], ["code"]
        at = 0
        while at < len(source):
            char = source[at]
            if contexts[-1] in ("'", '"'):
                if char == "\\":
                    kept.append(source[at : at + 2])
                    at += 2
                    continue
                if contexts[-1] == '"' and source.startswith("${", at):
                    contexts.append("splice")
                    kept.append("${")
                    at += 2
                    continue
                if char == contexts[-1]:
                    contexts.pop()
            elif char == "#":
                at = source.find("\n", at)
                kept.append(" ")
                if at < 0:
                    break
                continue
            elif char in ("'", '"'):
                contexts.append(char)
            elif contexts[-1] == "splice":
                if char == "{":
                    contexts.append("splice")
                elif char == "}":
                    contexts.pop()
            kept.append(char)
            at += 1
        source = "".join(kept)
    return re.sub(r"\s+", " ", source).strip()


def gz_size(path, language):
    return len(
        gzip.compress(stripped(path.read_text(), language).encode(), compresslevel=1)
    )


def peak(probe, command, stdin_path):
    """Peak resident memory in kilobytes, of a run of its own."""
    stdin = open(stdin_path, "rb") if stdin_path else subprocess.DEVNULL
    try:
        done = subprocess.run(
            [str(probe), "0", "-"] + command,
            stdin=stdin,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )
    finally:
        if stdin_path:
            stdin.close()
    if done.returncode:
        raise SystemExit(f"{command[0]} exited with status {done.returncode}")
    return int(done.stderr.decode().split()[-1])


def timed(command, stdin_path):
    stdin = open(stdin_path, "rb") if stdin_path else subprocess.DEVNULL
    try:
        start = time.perf_counter()
        done = subprocess.run(command, stdin=stdin, capture_output=True)
        elapsed = time.perf_counter() - start
    finally:
        if stdin_path:
            stdin.close()
    if done.returncode:
        raise SystemExit(f"{command[0]} exited with status {done.returncode}")
    return done.stdout, elapsed


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--faun", default=str(REPOSITORY / "target/release/faun"))
    parser.add_argument("--cc", default=os.environ.get("CC") or "gcc")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--game", action="store_true", help="the game's own sizes")
    parser.add_argument(
        "--only", default="", help="only benchmarks whose names hold this"
    )
    parser.add_argument("--cpu", type=int, help="pin every run to this idle CPU")
    args = parser.parse_args()
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    chosen = [b for b in BENCHMARKS if args.only in b[0]]
    if not chosen or args.runs < 1:
        parser.error("select at least one benchmark and a positive run count")
    rows = []
    with tempfile.TemporaryDirectory(prefix="faun-game-") as directory:
        work = Path(directory)
        probe = work / "peak"
        subprocess.run(
            [args.cc, "-O2", str(HERE / "measure.c"), "-o", str(probe)], check=True
        )
        built = {}
        for name, *_ in BENCHMARKS:
            if not any(name == c[0] for c in chosen) and not (
                name == "fasta" and any(c[0] == "k-nucleotide" for c in chosen)
            ):
                continue
            folder = HERE / name
            faun = work / f"{name}-faun"
            subprocess.run(
                [args.faun, "build", str(folder / "main.fn"), "-o", str(faun)],
                check=True,
                stdout=subprocess.DEVNULL,
            )
            c = work / f"{name}-c"
            subprocess.run(
                [args.cc, *C_FLAGS, str(folder / "main.c"), "-o", str(c), "-lm"]
                + C_LIBRARIES.get(name, []),
                check=True,
            )
            built[name] = (faun, c)
        for name, checked, game, quick in chosen:
            faun, c = built[name]
            size = game if args.game else quick
            folder = HERE / name
            stdin_for = lambda n: None
            if name == "k-nucleotide":
                inputs = {}
                for n in (checked, size):
                    path = work / f"fasta-{n}.txt"
                    path.write_bytes(timed([str(built["fasta"][1]), str(n)], None)[0])
                    inputs[n] = path
                stdin_for = inputs.get
                arguments = lambda n: []
            else:
                arguments = lambda n: [str(n)]
            expected = (folder / f"{checked}.out").read_bytes()
            said, _ = timed([str(faun)] + arguments(checked), stdin_for(checked))
            if said != expected:
                raise SystemExit(
                    f"{name}: Faun's output at {checked} is not the game's"
                )
            expected = None
            times = {"faun": [], "c": []}
            for trial in range(args.runs):
                order = [("faun", faun), ("c", c)]
                for language, image in order[:: 1 if trial % 2 == 0 else -1]:
                    output, seconds = timed(
                        [str(image)] + arguments(size), stdin_for(size)
                    )
                    if expected is None:
                        expected = output
                    elif output != expected:
                        raise SystemExit(f"{name}: {language} output at {size} differs")
                    times[language].append(seconds)
            for language, image in (("faun", faun), ("c", c)):
                rows.append(
                    (
                        name,
                        size,
                        language,
                        min(times[language]),
                        peak(probe, [str(image)] + arguments(size), stdin_for(size)),
                        gz_size(
                            folder / ("main.fn" if language == "faun" else "main.c"),
                            language,
                        ),
                    )
                )
    report(rows)


def report(rows):
    print(
        f"{'benchmark':15} {'n':>9}  {'secs':>7} {'×':>6}  {'mem KB':>9} {'×':>6}  {'gz':>5} {'×':>5}"
    )
    by = {}
    for name, size, language, seconds, memory, gz in rows:
        by.setdefault(name, {})[language] = (size, seconds, memory, gz)
    for name, sides in by.items():
        size, seconds, memory, gz = sides["faun"]
        _, c_seconds, c_memory, c_gz = sides["c"]
        print(
            f"{name:15} {size:>9}  {seconds:7.2f} {seconds / c_seconds:5.1f}x  "
            f"{memory:9,} {memory / c_memory:5.1f}x  {gz:5} {gz / c_gz:4.1f}x"
        )
        print(
            f"{'  C':15} {'':>9}  {c_seconds:7.2f} {'':>6}  {c_memory:9,} {'':>6}  {c_gz:5}"
        )


if __name__ == "__main__":
    main()
