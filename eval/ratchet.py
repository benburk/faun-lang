"""Score a candidate revision of the compiler against the incumbent.

Each side is a checkout directory, built in place, or a git revision, exported
into a cache and built there; no git worktrees are created. Both compile the
suite's programs for every target, with each backend, favouring speed and
favouring size. A program must print what its C twin prints, and is then
measured beside it: the instructions, fuel or cycles it ran, the memory it
used, and the bytes of its image. See RATCHET.md for the rules.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import secrets
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from typing import NamedTuple

ROOT = Path(__file__).resolve().parents[1]
PROTECTED = [
    line
    for line in (ROOT / "eval/protected.txt").read_text().splitlines()
    if line and not line.startswith("#")
]
# The repository being evaluated; the pinned evaluator runs from an export.
REPO = Path(os.environ.get("RATCHET_REPO", ROOT))
CACHE = Path(os.environ.get("RATCHET_CACHE", Path.home() / ".cache/faun-ratchet"))
# What is merged into the trunk is what was approved: its evaluator judges,
# and it is the incumbent of a branch that has had nothing accepted yet.
APPROVED = "origin/main"
TRUNK = os.environ.get("RATCHET_TRUNK", APPROVED)

X86, WASM, MOS = "x86_64-linux", "wasm32-wasi", "mos6502-sim65"
TARGETS = (X86, WASM, MOS)
BACKENDS = ("stock", "lab")
# What is measured of a program: how long it ran, in the target's own steady
# count; its peak memory; its image built for speed; its image built `--small`;
# and the instructions the compiler ran to build both.
METRICS = ("speed", "memory", "size", "small", "compile")
UNITS = {
    X86: ("instructions", "KiB resident", "bytes", "bytes", "instructions"),
    WASM: ("fuel", "bytes of linear memory touched", "bytes", "bytes", "instructions"),
    MOS: ("cycles", "bytes written", "bytes", "bytes", "instructions"),
}

# The rules RATCHET.md states. Each metric of each target weighs the same, and
# compiling, which runs on this machine whatever the target, is one more group.
WEIGHTS = {"speed": 1, "memory": 1, "size": 1, "small": 1, "compile": 1}
WORST = 1.10  # no cell may be more than 10% worse
COMPILE_WORST = 1.25  # nor any build take a quarter more instructions
MINIMUM = 0.001  # a gain below a tenth of a percent overall is neutral
# A memory this little larger is not past that, however small it was: four
# pages, and half a page of the 6502's.
SLACK = {(X86, "memory"): 16, (WASM, "memory"): 16 << 10, (MOS, "memory"): 128}
MARGIN = 2.0  # gains must outweigh losses this many times over
REPAIRED = 0.5  # a cell that starts working counts as a halving
# The counts that are not exact. A program's x86 instructions vary in their
# last digits, by a part in ten million where measured, so one in a hundred
# thousand is the same. The compiler's vary by about a part in a hundred, from
# the order its hash tables are seeded in, so two in a hundred are the same.
SAME = {(X86, "speed"): lambda old, new: abs(new - old) <= old * 1e-5}
for _target in TARGETS:
    SAME[(_target, "compile")] = lambda old, new: abs(new - old) <= old * 2e-2
# A timed candidate is slower where its quickest and its median run are both
# past this band over the incumbent's: a tenth, and a quarter of a millisecond.
TURNS, SLOWER, FLOOR_NS, TIMED_NS = 5, 1.10, 250_000, 250_000_000

SECONDS = 120  # one run's limit
FUEL = 200_000_000_000
CYCLES = 4_000_000_000

GAME = ROOT / "crates/faun/examples/benchmarks-game"
KERNELS = ROOT / "eval/workloads"


class Workload(NamedTuple):
    """A program in Faun and its C twin, `main.fn` and `main.c` in a folder.

    `input` says what a size means: an `argument`; `fasta`, that the C fasta's
    output of that size is standard input; or `bytes`, that so many seeded
    random bytes are. `sizes` holds the size measured on each target: small
    enough to take a fraction of a second, since the counts do not vary.
    """

    name: str
    folder: Path
    input: str
    sizes: dict
    step: int = 1
    libraries: tuple = ()


def sizes(x86, wasm, mos):
    return {X86: x86, WASM: wasm, MOS: mos}


WORKLOADS = [
    Workload("binary-trees", GAME, "argument", sizes(14, 12, 4)),
    Workload("fannkuch-redux", GAME, "argument", sizes(8, 8, 5)),
    Workload("fasta", GAME, "argument", sizes(100_000, 100_000, 50)),
    Workload("k-nucleotide", GAME, "fasta", sizes(2500, 1000, 100)),
    Workload("mandelbrot", GAME, "argument", sizes(400, 12, 4)),
    Workload("md5", GAME, "bytes", sizes(1 << 20, 1 << 18, 256)),
    Workload("n-body", GAME, "argument", sizes(200_000, 50, 2)),
    # The C twin leaves out a last line of fewer than ten digits.
    Workload("pidigits", GAME, "argument", sizes(500, 300, 20), 10, ("-lgmp",)),
    Workload("spectral-norm", GAME, "argument", sizes(300, 6, 2)),
    Workload("checksum", KERNELS, "bytes", sizes(1 << 22, 1 << 20, 1024)),
    Workload("collatz", KERNELS, "argument", sizes(20_000, 10_000, 100)),
    Workload("queens", KERNELS, "argument", sizes(9, 8, 6)),
    Workload("sieve", KERNELS, "argument", sizes(1_000_000, 500_000, 1000)),
    Workload("sort", KERNELS, "argument", sizes(100_000, 30_000, 24)),
]


def git(*args, cwd=None):
    return subprocess.check_output(["git", *args], cwd=cwd or REPO, text=True).strip()


def main_checkout():
    return Path(git("rev-parse", "--path-format=absolute", "--git-common-dir")).parent


# Reports live in the main checkout, so they outlast per-idea worktrees.
REPORTS = Path(os.environ.get("RATCHET_REPORTS", main_checkout() / "ratchet/reports"))


def holds(commit, ancestor):
    """Whether a commit's history holds another: no, where either is unknown."""
    asked = ["git", "merge-base", "--is-ancestor", ancestor, commit]
    return subprocess.run(asked, cwd=REPO, capture_output=True).returncode == 0


def incumbent_of(candidate):
    """The revision a candidate must beat: the newest commit its branch's log
    calls accepted, where the trunk does not hold that commit yet, and
    otherwise the trunk. The log and the trunk are the record; no tag is."""
    shown = subprocess.run(
        ["git", "show", f"{candidate.commit}:ratchet/log.tsv"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    rows = csv.DictReader(shown.stdout.splitlines(), delimiter="\t")
    accepted = [
        row.get("commit") or ""
        for row in rows
        if (row.get("verdict") or "").startswith(("accept", "override"))
    ]
    newest = accepted[-1] if accepted else ""
    if holds(candidate.commit, newest) and not holds(TRUNK, newest):
        return newest
    return TRUNK


def export(commit, dest):
    """Write a commit's tree to dest without creating a worktree."""
    dest.mkdir(parents=True)
    archive = subprocess.Popen(
        ["git", "archive", commit], cwd=REPO, stdout=subprocess.PIPE
    )
    subprocess.run(["tar", "-x", "-C", str(dest)], stdin=archive.stdout, check=True)
    if archive.wait():
        sys.exit(f"git archive failed for {commit}")


def sha(path):
    with open(path, "rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


class Side:
    """A checkout directory built in place, or a revision exported once into
    the cache. Neither creates a git worktree."""

    def __init__(self, spec):
        self.spec = spec
        if Path(spec).is_dir():
            self.path = Path(spec).resolve()
            self.commit = git("rev-parse", "HEAD", cwd=self.path)
            self.dirty = bool(
                git("status", "--porcelain", "--untracked-files=no", cwd=self.path)
            )
            self.target = self.path / "target"
            self.binary = self.target / "release/faun"
        else:
            found = subprocess.run(
                ["git", "rev-parse", "--verify", "--quiet", f"{spec}^{{commit}}"],
                cwd=REPO,
                capture_output=True,
                text=True,
            )
            if found.returncode:
                sys.exit(f"`{spec}` is neither a checkout nor a revision")
            self.commit = found.stdout.strip()
            self.dirty = False
            self.path = CACHE / "trees" / self.commit
            if not self.path.exists():
                export(self.commit, self.path)
            # Exports share one target directory so dependencies build once.
            self.target = CACHE / "target"
            self.binary = CACHE / "bin" / self.commit / "faun"

    def build(self):
        cached = self.target == CACHE / "target"
        if cached and self.binary.exists():
            return
        subprocess.run(
            ["cargo", "build", "--locked", "--release", "--quiet", "-p", "faun-cli"],
            cwd=self.path,
            env=os.environ | {"CARGO_TARGET_DIR": str(self.target)},
            check=True,
        )
        if cached:
            self.binary.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(self.target / "release/faun", self.binary)

    def describe(self):
        return {
            "spec": self.spec,
            "commit": self.commit,
            "dirty": self.dirty,
            "compiler_sha256": sha(self.binary),
        }


def protected_changes(candidate, evaluator):
    """Protected paths the candidate changed since its branch left the
    approved evaluator's history."""
    base = git("merge-base", evaluator, candidate.commit)
    against = [candidate.commit] if not candidate.dirty else []
    cwd = candidate.path if candidate.dirty else None
    return git("diff", "--name-only", base, *against, "--", *PROTECTED, cwd=cwd).split()


def first_line(text, wanted="error"):
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    chosen = [line for line in lines if wanted in line.lower()] or lines
    return chosen[0][:200] if chosen else "no message"


def run(target, image, arguments, stdin, out):
    """Run an image in its own directory and under its own name, so that the
    path a program is told it has is the same for both sides. Answers its
    status, `ok` where it left with zero and nothing on standard error, and
    what it took."""
    tools = Path(os.environ["RATCHET_TOOLS"])
    metrics = out.with_suffix(".metrics")
    name = f"./{image.name}"
    env = {}
    if target == X86:
        command = [tools / "measure", str(SECONDS), metrics, name, *arguments]
    elif target == WASM:
        command = [sys.executable, ROOT / "eval/wasm.py", name]
        command += [stdin or os.devnull, out, str(FUEL), *arguments]
    else:
        command = [os.environ["SIM65"], "-x", str(CYCLES), name, *arguments]
        env = {"SIM65_METRICS": "1"}
    with open(stdin or os.devnull, "rb") as source, open(out, "wb") as sink:
        try:
            done = subprocess.run(
                command,
                cwd=image.parent,
                env=env,
                stdin=source,
                stdout=subprocess.PIPE if target == WASM else sink,
                stderr=subprocess.PIPE,
                timeout=SECONDS + 30,
            )
        except subprocess.TimeoutExpired:
            return {"status": "timeout"}
    errors = done.stderr.decode(errors="replace")
    code, taken = done.returncode, {}
    if target == X86 and code == 0:
        ns, rss, instructions, cpu = map(int, metrics.read_text().split())
        taken = {"speed": instructions if instructions >= 0 else None}
        taken |= {"memory": rss, "ns": ns, "cpu_ns": cpu}
    elif target == WASM and code == 0:
        code, fuel, held, ns = map(int, done.stdout.split())
        taken = {"speed": fuel, "memory": held, "ns": ns}
    elif target == MOS:
        told = re.search(r"^sim65 cycles (\d+) written (\d+)\n", errors, re.M)
        if told:
            taken = {"speed": int(told[1]), "memory": int(told[2])}
            errors = errors.replace(told[0], "")
    if code:
        return {"status": f"exit {code}: {first_line(errors)}"}
    if errors.strip():
        return {"status": f"standard error: {first_line(errors)}"}
    return {"status": "ok", "stdout": sha(out)} | taken


def c_command(target, workload, source, out):
    include = f"-I{source.parent}"
    if target == X86:
        flags = ["-O3", "-fomit-frame-pointer", "-s", include]
        return ["gcc", *flags, source, "-o", out, "-lm", *workload.libraries], out
    if target == WASM:
        out = out.with_suffix(".wasm")
        # wasm-ld's stack is 64 KiB unless told, less than md5's one buffer.
        flags = ["-O3", "-Wl,--strip-all", "-Wl,-z,stack-size=262144", include]
        return [os.environ["WASI_CC"], *flags, source, "-o", out, "-lm"], out
    out = out.with_suffix(".bin")
    return ["cl65", "-t", "sim6502", "-O", source, "-o", out], out


def c_build(target, workload, directory):
    """The C twin's image for a target, or why there is none: cc65 has no
    floats, and there is no GMP for wasm32 or the 6502."""
    directory.mkdir(parents=True, exist_ok=True)
    # cl65 leaves its object files beside the source, so compile a copy.
    copy = directory / f"{workload.name}-source"
    shutil.copytree(workload.folder / workload.name, copy)
    command, image = c_command(
        target, workload, copy / "main.c", directory / workload.name
    )
    done = subprocess.run(command, capture_output=True, text=True, timeout=SECONDS)
    if done.returncode:
        return None, first_line(done.stderr)
    return image, "ok"


class Oracle:
    """What each program must print: what its C twin, built for this machine,
    prints for the same input. Also makes the inputs."""

    def __init__(self, work, workloads, pool):
        self.work = work / "oracle"
        self.known = {}
        # k-nucleotide reads what the C fasta writes.
        fasta = next(w for w in WORKLOADS if w.name == "fasta")
        needed = {w.name: w for w in [*workloads, fasta]}.values()
        built = pool.map(lambda w: c_build(X86, w, self.work), needed)
        self.images = {}
        for workload, (image, why) in zip(needed, built):
            if image is None:
                sys.exit(f"{workload.name}: the C twin does not build: {why}")
            self.images[workload.name] = image

    def case(self, workload, size):
        """The arguments and standard input of a size, and the output's hash."""
        key = workload.name, size
        if key not in self.known:
            arguments, stdin = [str(size)], None
            if workload.input != "argument":
                arguments, stdin = [], self.work / f"{workload.name}-{size}.in"
            if workload.input == "bytes":
                stdin.write_bytes(
                    random.Random(f"{workload.name}:{size}").randbytes(size)
                )
            elif workload.input == "fasta":
                made = run(X86, self.images["fasta"], [str(size)], None, stdin)
                if made["status"] != "ok":
                    sys.exit(f"fasta {size}: {made['status']}")
            out = self.work / f"{workload.name}-{size}.out"
            said = run(X86, self.images[workload.name], arguments, stdin, out)
            if said["status"] != "ok":
                sys.exit(f"{workload.name} {size}: the C twin: {said['status']}")
            self.known[key] = arguments, stdin, said
        return self.known[key]


def faun_build(side, target, backend, small, workload, directory):
    """Build a workload, answering its image or why there is none, and its
    size: for a 6502 image past the machine's 64 KiB, where it would end."""
    directory.mkdir(parents=True, exist_ok=True)
    command = [side.binary, "build", f"--target={target}"]
    # Stock is the default, and a revision before the flag has only it.
    if backend != "stock":
        command.append(f"--backend={backend}")
    if small:
        command.append("--small")
    source = workload.folder / workload.name / "main.fn"
    command += [source, "-o", directory / workload.name]
    # The compiler is measured as a program is: its instructions, its time
    # and its peak memory.
    # Each workload's own file: the cells of a target build side by side here.
    metrics = directory / f"{workload.name}.build-metrics"
    probe = Path(os.environ["RATCHET_TOOLS"]) / "measure"
    command = [probe, str(SECONDS), metrics, *command]
    env = {k: v for k, v in os.environ.items() if k != "FAUN_STD"}
    try:
        done = subprocess.run(
            command, env=env, capture_output=True, text=True, timeout=SECONDS + 30
        )
    except subprocess.TimeoutExpired:
        return None, "build: timeout", None, {}
    taken = {}
    if metrics.exists():
        ns, rss, instructions, cpu = map(int, metrics.read_text().split())
        taken = {"instructions": instructions, "ns": ns, "rss_kib": rss}
    wrote = re.search(r"^wrote (.+)$", done.stdout, re.M)
    if done.returncode or not wrote:
        past = re.search(r"image ends at \$([0-9A-F]+), past", done.stderr)
        if past:
            return None, "too large", int(past[1], 16), taken
        return None, f"build: {first_line(done.stderr)}", None, taken
    image = Path(wrote[1])
    return image, "ok", image.stat().st_size, taken


def faun_cell(side, label, target, backend, workload, check, oracle, work):
    """Build a workload both ways for one target and backend, hold both
    images to the oracle at a seeded size, and measure the one built for
    speed at the target's size."""
    directory = work / label / target / backend
    cell = {"status": "ok"}
    images, builds = {}, {}
    for metric, small in (("size", False), ("small", True)):
        image, status, size, builds[metric] = faun_build(
            side, target, backend, small, workload, directory / metric
        )
        cell[metric] = size
        if image is None:
            cell["status"] = status
        else:
            images[metric] = image
            cell[f"{metric}_sha256"] = sha(image)
    counts = [build.get("instructions", -1) for build in builds.values()]
    if all(count > 0 for count in counts):
        cell["compile"] = sum(counts)
        cell["compile_ns"] = sum(build["ns"] for build in builds.values())
        cell["compile_rss_kib"] = max(build["rss_kib"] for build in builds.values())
    if cell["status"] != "ok":
        return cell
    arguments, stdin, expected = oracle.case(workload, check)
    for metric, image in images.items():
        said = run(target, image, arguments, stdin, image.with_suffix(".check"))
        if said["status"] == "ok" and said["stdout"] != expected["stdout"]:
            said["status"] = "wrong output"
        if said["status"] != "ok":
            cell["status"] = f"{metric} image at {check}: {said['status']}"
            return cell
    arguments, stdin, expected = oracle.case(workload, workload.sizes[target])
    image = images["size"]
    said = run(target, image, arguments, stdin, image.with_suffix(".out"))
    if said["status"] == "ok" and said["stdout"] != expected["stdout"]:
        said["status"] = "wrong output"
    if said["status"] != "ok":
        cell["status"] = f"at {workload.sizes[target]}: {said['status']}"
        return cell
    return (
        cell
        | {k: said.get(k) for k in ("speed", "memory", "ns")}
        | {"image": str(image)}
    )


def c_cell(target, workload, oracle, work):
    """The C twin's measures on a target, where it builds and agrees there."""
    image, status = c_build(target, workload, work / "c" / target)
    if image is None:
        return {"status": f"build: {status}"}
    arguments, stdin, expected = oracle.case(workload, workload.sizes[target])
    said = run(target, image, arguments, stdin, image.with_suffix(".out"))
    if said["status"] == "ok" and said["stdout"] != expected["stdout"]:
        said["status"] = "wrong output"
    if said["status"] != "ok":
        return {"status": said["status"]}
    size = image.stat().st_size
    measures = {k: said.get(k) for k in ("speed", "memory", "ns")}
    return {"status": "ok", "size": size, "small": size, "image": str(image)} | measures


def timed(cpu, cells, oracle):
    """Processor times of the x86 images, pinned to one CPU. The sides take
    turns, one run each in turning order, for as many turns as take the
    incumbent a quarter of a second. Whatever else the CPU is doing can only
    lengthen a run, so a side's time is its quickest, kept with its median."""
    allowed = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    for (target, backend, name), sides in cells.items():
        ready = {k: v for k, v in sides.items() if v.get("image")}
        if target != X86 or "candidate" not in ready or "incumbent" not in ready:
            continue
        workload = next(w for w in WORKLOADS if w.name == name)
        arguments, stdin, _ = oracle.case(workload, workload.sizes[target])

        def once(side):
            image = Path(ready[side]["image"])
            said = run(X86, image, arguments, stdin, image.with_suffix(".timed"))
            return said.get("cpu_ns") or math.inf

        order = list(ready)
        # The first run of each only warms it, and says how long one takes.
        warm = {side: once(side) for side in order}
        turns = max(TURNS, min(10 * TURNS, math.ceil(TIMED_NS / warm["incumbent"])))
        samples = {side: [] for side in order}
        for turn in range(turns):
            at = turn % len(order)
            for side in order[at:] + order[:at]:
                samples[side].append(once(side))
        for side, times in samples.items():
            if math.isfinite(min(times)):
                sides[side]["time"] = min(times)
                sides[side]["time_median"] = statistics.median(times)
    os.sched_setaffinity(0, allowed)


def slower(incumbent, candidate):
    """Whether a timed candidate is slower beyond the noise: both its quickest
    run and its median run past the band over the incumbent's. On a busy CPU
    a lucky run fools the quickest and a burst fools the median, seldom both."""
    if incumbent.get("size_sha256") == candidate.get("size_sha256"):
        return False

    def past(measure):
        old, new = incumbent.get(measure), candidate.get(measure)
        return bool(old and new) and new > max(old * SLOWER, old + FLOOR_NS)

    return past("time") and past("time_median")


def ratio(target, metric, incumbent, candidate):
    """A cell's candidate over its incumbent: below one is better. `None`
    where neither side has the measure, `broken` where only the incumbent
    does, and a halving where only the candidate does."""
    old, new = incumbent.get(metric), candidate.get(metric)
    if old is None and new is None:
        return None
    if new is None:
        return "broken"
    if old is None:
        return REPAIRED
    # The same image did the same work, whatever a count's last digits say.
    unchanged = incumbent.get("size_sha256") == candidate.get("size_sha256")
    if old == new or (unchanged and metric in ("speed", "memory")):
        return 1.0
    close = SAME.get((target, metric))
    if close and close(old, new):
        return 1.0
    # A measure of nothing, such as memory never written, has no ratio.
    return new / old if old and new else None


def score(cells):
    """Weigh every cell's ratio into one score, the geometric mean of the
    candidate over the incumbent with each target's metric counting the same,
    and split it into the gain of the better cells and the loss of the worse."""
    changes, broken = [], []
    for (target, backend, name), sides in sorted(cells.items()):
        for metric in METRICS:
            change = ratio(target, metric, sides["incumbent"], sides["candidate"])
            where = {
                "target": target,
                "backend": backend,
                "workload": name,
                "metric": metric,
            }
            if change == "broken":
                broken.append(where | {"status": sides["candidate"]["status"]})
            elif change is not None:
                old, new = sides["incumbent"].get(metric), sides["candidate"][metric]
                changes.append(where | {"ratio": change, "old": old, "new": new})
    groups = {}
    for change in changes:
        # Compiling runs here whatever the target, so it is one group.
        target = "all" if change["metric"] == "compile" else change["target"]
        groups.setdefault((target, change["metric"]), []).append(change)
    total = sum(WEIGHTS[metric] for _, metric in groups) or 1
    gain = loss = 0.0
    for (_, metric), members in groups.items():
        for change in members:
            share = WEIGHTS[metric] / total / len(members) * math.log(change["ratio"])
            gain -= min(share, 0.0)
            loss += max(share, 0.0)
    return {
        "score": math.exp(loss - gain),
        "gain": gain,
        "loss": loss,
        "groups": {
            f"{target} {metric}": geomean(c["ratio"] for c in members)
            for (target, metric), members in sorted(groups.items())
        },
        "better": sum(c["ratio"] < 1 for c in changes),
        "worse": sum(c["ratio"] > 1 for c in changes),
        "changed": sorted(
            (c for c in changes if c["ratio"] != 1), key=lambda c: c["ratio"]
        ),
        "broken": broken,
    }


def geomean(ratios):
    logs = [math.log(r) for r in ratios]
    return math.exp(sum(logs) / len(logs)) if logs else None


def decide(scored, protected=(), slowed=()):
    """The verdict and its reasons, as RATCHET.md states them."""
    reasons = []
    if protected:
        reasons.append("changes protected paths: " + ", ".join(protected))
    for cell in scored["broken"]:
        reasons.append("breaks " + place(cell) + f" ({cell['status']})")
    for cell in scored["changed"]:
        slack = SLACK.get((cell["target"], cell["metric"]), 0)
        worst = COMPILE_WORST if cell["metric"] == "compile" else WORST
        if cell["ratio"] > worst and cell["new"] - cell["old"] > slack:
            reasons.append(f"{place(cell)} is {cell['ratio'] - 1:.1%} worse")
    for cell in slowed:
        reasons.append(f"{place(cell)} runs {cell['ratio'] - 1:.1%} longer")
    gain, loss = scored["gain"], scored["loss"]
    if not gain and not loss:
        return ("reject", reasons) if reasons else ("no change", [])
    if gain < MARGIN * loss:
        reasons.append(
            f"gain {gain:.5f} does not outweigh loss {loss:.5f} {MARGIN:g} to 1"
        )
    if reasons:
        return "reject", reasons
    if gain - loss < MINIMUM:
        return "neutral", [f"net gain {gain - loss:.5f} is below {MINIMUM:g}"]
    return "accept", []


def place(cell):
    return f"{cell['target']} {cell['backend']} {cell['workload']} {cell['metric']}"


def tools(work):
    """Build the x86 probe, and say what measures."""
    subprocess.run(
        ["gcc", "-O2", ROOT / "eval/measure.c", "-o", work / "measure"], check=True
    )
    os.environ["RATCHET_TOOLS"] = str(work)

    def version(*command):
        said = subprocess.run(command, capture_output=True, text=True)
        return (said.stdout + said.stderr).strip().splitlines()[0]

    return {
        "gcc": version("gcc", "--version"),
        "wasi_cc": version(os.environ["WASI_CC"], "--version"),
        "cl65": version("cl65", "--version"),
        "sim65": os.environ["SIM65"],
        "wasmtime": importlib.metadata.version("wasmtime"),
        "python": platform.python_version(),
    }


def machine():
    model = next(
        (
            line.split(":", 1)[1].strip()
            for line in Path("/proc/cpuinfo").read_text().splitlines()
            if line.startswith("model name")
        ),
        platform.machine(),
    )
    return {
        "cpu": model,
        "cores": os.cpu_count(),
        "kernel": platform.release(),
        "load": os.getloadavg()[0],
    }


def measure(sides, seed, jobs, only, work):
    """Every cell of the suite for each side, and the C twins beside them."""
    chosen = [w for w in WORKLOADS if only in w.name]
    pool = ThreadPoolExecutor(jobs)
    oracle = Oracle(work, chosen, pool)
    checks = {}
    for workload in chosen:
        for target in TARGETS:
            # A different size from the one measured, fresh with each seed.
            most = workload.sizes[target] // workload.step
            drawn = random.Random(f"{seed}:{workload.name}:{target}")
            checks[workload.name, target] = workload.step * drawn.randint(
                max(1, most // 3), max(1, most - 1)
            )

    # Each workload's inputs and answers are made once, here, before two of
    # its cells could ask for the same one.
    def cases(workload):
        for target in TARGETS:
            oracle.case(workload, workload.sizes[target])
            oracle.case(workload, checks[workload.name, target])

    list(pool.map(cases, chosen))
    cells = {}
    with pool:
        for workload in chosen:
            for target in TARGETS:
                c = pool.submit(c_cell, target, workload, oracle, work)
                for backend in BACKENDS:
                    key = target, backend, workload.name
                    cells[key] = {"c": c}
                    check = checks[workload.name, target]
                    for label, side in sides.items():
                        cells[key][label] = pool.submit(
                            faun_cell,
                            side,
                            label,
                            target,
                            backend,
                            workload,
                            check,
                            oracle,
                            work,
                        )
        cells = {
            key: {label: pending.result() for label, pending in found.items()}
            for key, found in cells.items()
        }
    return cells, checks, oracle


def table(cells, scored):
    """The summary printed after a run: each target and backend's geometric
    mean change, and how the candidate stands against C."""
    lines = [f"{'':22}" + "".join(f"{metric:>18}" for metric in METRICS)]
    lines.append(f"{'':22}" + f"{'change':>10}{'x C':>8}" * len(METRICS))
    for target in TARGETS:
        for backend in BACKENDS:
            row = f"{target + ' ' + backend:22}"
            for metric in METRICS:
                changes, against = [], []
                for (t, b, _), sides in cells.items():
                    if (t, b) != (target, backend):
                        continue
                    change = ratio(t, metric, sides["incumbent"], sides["candidate"])
                    if isinstance(change, float):
                        changes.append(change)
                    ours, theirs = (
                        sides["candidate"].get(metric),
                        sides["c"].get(metric),
                    )
                    if sides["candidate"]["status"] == "ok" and ours and theirs:
                        against.append(ours / theirs)
                change, c = geomean(changes), geomean(against)
                row += f"{change - 1:>+10.2%}" if change else f"{'-':>10}"
                row += f"{c:>8.2f}" if c else f"{'-':>8}"
            lines.append(row)
    for cell in scored["changed"][:12] + scored["changed"][12:][-12:]:
        lines.append(f"  {cell['ratio'] - 1:+8.2%}  {place(cell)}")
    failing = sorted(
        (key, sides["candidate"]["status"])
        for key, sides in cells.items()
        if sides["candidate"]["status"] != "ok"
    )
    for (target, backend, name), status in failing:
        lines.append(f"  not running: {target} {backend} {name}: {status}")
    return "\n".join(lines)


def short(count):
    """A count in three figures: K, M and G are thousands, millions, billions."""
    for unit, size in (("G", 1e9), ("M", 1e6), ("K", 1e3)):
        if count >= size:
            return f"{count / size:.3g}{unit}"
    return str(count)


def times(ours, theirs):
    """How many times the C twin's measure ours is, where both have one."""
    if not ours or not theirs:
        return "-"
    x = ours / theirs
    return (
        f"{x / 1000:.2g}k" if x >= 999.5 else f"{x:.3g}" if x >= 9.995 else f"{x:.2f}"
    )


def standings(report):
    """A report's candidate against the C twins, as Markdown: a table for
    each target and backend, and under it what does not run there."""
    commit = report["candidate"]["commit"][:7]
    lines = [
        "# Standings",
        "",
        f"Faun at `{commit}` beside each program's C twin, from the report of",
        f"{report['started'][:10]}; `just standings` writes this file and",
        "[RATCHET.md](../RATCHET.md) says what is measured. Speed is counted in",
        "instructions on x86-64, fuel on wasm32 and cycles on the 6502; memory",
        "and sizes are bytes. K, M and G are thousands, millions and billions.",
        "`vs C` is Faun's measure over the C twin's: below one, Faun is ahead.",
    ]
    for target in TARGETS:
        for backend in BACKENDS:
            cells = [
                c
                for c in report["cells"]
                if (c["target"], c["backend"]) == (target, backend)
            ]
            rows = [
                ["Program", "Speed", "vs C", "Memory", "vs C", "Size", "vs C", "Small"]
            ]
            ratios, failing = {"speed": [], "memory": [], "size": []}, []
            for cell in cells:
                ours, c = cell["candidate"], cell["c"]
                if ours["status"] != "ok":
                    failing.append(f"{cell['workload']}: {ours['status']}")
                    continue
                # x86-64 memory is measured in KiB.
                scale = 1024 if target == X86 else 1
                row = [
                    cell["workload"],
                    short(ours["speed"]),
                    times(ours["speed"], c.get("speed")),
                ]
                row += [
                    short(ours["memory"] * scale),
                    times(ours["memory"], c.get("memory")),
                ]
                row += [
                    f"{ours['size']:,}",
                    times(ours["size"], c.get("size")),
                    f"{ours['small']:,}",
                ]
                rows.append(row)
                for metric, held in ratios.items():
                    if ours[metric] and c.get(metric):
                        held.append(ours[metric] / c[metric])
            means = {metric: geomean(held) for metric, held in ratios.items()}
            mean = ["geometric mean", ""] + [times(means["speed"], 1), ""]
            rows.append(
                mean + [times(means["memory"], 1), "", times(means["size"], 1), ""]
            )
            widths = [max(len(row[at]) for row in rows) for at in range(len(rows[0]))]
            rows.insert(1, ["-" * width for width in widths])
            lines += ["", f"## {target}, {backend}", ""]
            for row in rows:
                padded = (cell.ljust(width) for cell, width in zip(row, widths))
                lines.append("| " + " | ".join(padded) + " |")
            if failing:
                lines += ["", "Not running:", ""] + [
                    f"- {program}" for program in failing
                ]
    return "\n".join(lines) + "\n"


def evaluate(args):
    kind = "noise" if args.command == "noise" else "eval"
    candidate = Side(args.candidate if kind == "eval" else ".")
    incumbent = Side(args.incumbent or incumbent_of(candidate))
    if kind == "noise":
        candidate = incumbent
    print(f"incumbent: {incumbent.spec}, {incumbent.commit[:7]}", file=sys.stderr)
    evaluator = os.environ.get("RATCHET_EVAL_COMMIT")
    protected = []
    if evaluator and kind == "eval" and not args.allow_protected:
        protected = protected_changes(candidate, evaluator)
    for side in {candidate, incumbent}:
        side.build()
    seed = args.seed if args.seed is not None else secrets.randbits(32)
    started = time.time()
    with tempfile.TemporaryDirectory(prefix="faun-ratchet-") as directory:
        work = Path(directory)
        report = {
            "schema": 1,
            "kind": kind,
            "started": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "evaluator": evaluator or f"unpinned {git('rev-parse', 'HEAD', cwd=ROOT)}",
            "candidate": candidate.describe(),
            "incumbent": incumbent.describe(),
            "machine": machine(),
            "tools": tools(work),
            "seed": seed,
            "rules": {
                "weights": WEIGHTS,
                "worst": WORST,
                "margin": MARGIN,
                "compile_worst": COMPILE_WORST,
                "minimum": MINIMUM,
                "repaired": REPAIRED,
                "slower": SLOWER,
            },
        }
        sides = {"candidate": candidate, "incumbent": incumbent}
        cells, checks, oracle = measure(sides, seed, args.jobs, args.only, work)
        if args.time is not None:
            timed(args.time, cells, oracle)
    scored = score(cells)
    slowed = [
        {"target": t, "backend": b, "workload": w, "metric": "time"}
        | {"ratio": sides["candidate"]["time"] / sides["incumbent"]["time"]}
        for (t, b, w), sides in sorted(cells.items())
        if slower(sides["incumbent"], sides["candidate"])
    ]
    verdict, reasons = decide(scored, protected, slowed)
    # What keeps even an accepted run from being a promotion.
    caveats = []
    if kind == "noise":
        # The same compiler twice: any difference is the evaluator's noise.
        verdict = "quiet" if verdict == "no change" else "noisy"
    else:
        if not evaluator:
            caveats.append("unpinned evaluator")
        if TRUNK != APPROVED:
            caveats.append(f"the trunk was taken to be {TRUNK}")
        if candidate.dirty:
            caveats.append("uncommitted changes in the candidate")
        if args.only:
            caveats.append(f"only the workloads holding `{args.only}`")
    report |= {
        "seconds": round(time.time() - started, 1),
        "timed_cpu": args.time,
        "sizes": {w.name: w.sizes for w in WORKLOADS},
        "checks": {f"{name} {target}": size for (name, target), size in checks.items()},
        "units": {target: dict(zip(METRICS, units)) for target, units in UNITS.items()},
        "cells": [
            {"target": t, "backend": b, "workload": w}
            | {
                label: {k: v for k, v in side.items() if k != "image"}
                for label, side in sides.items()
            }
            for (t, b, w), sides in sorted(cells.items())
        ],
        "slowed": slowed,
        "verdict": verdict,
        "reasons": reasons,
        "caveats": caveats,
    } | scored
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    REPORTS.mkdir(parents=True, exist_ok=True)
    path = (
        REPORTS
        / f"{stamp}-{kind}-{candidate.commit[:8]}-vs-{incumbent.commit[:8]}.json"
    )
    with path.open("x") as file:
        json.dump(report, file, indent=1)
        file.write("\n")
    print(table(cells, scored))
    summary = {
        "verdict": verdict,
        "reasons": reasons,
        "not a promotion": caveats,
        "score": round(scored["score"], 5),
        "better": scored["better"],
        "worse": scored["worse"],
        "worst": round(max((c["ratio"] for c in scored["changed"]), default=1.0), 5),
        "seconds": report["seconds"],
        "report": str(path),
    } | {
        # Each metric's change, the geometric mean of its targets' means.
        metric: round(
            geomean(v for k, v in scored["groups"].items() if k.endswith(metric)) or 1,
            5,
        )
        for metric in METRICS
    }
    print(json.dumps(summary, indent=1))
    return verdict == "quiet" or (verdict == "accept" and not caveats)


def parser():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    for name in ("eval", "noise"):
        s = sub.add_parser(name)
        if name == "eval":
            s.add_argument(
                "candidate",
                nargs="?",
                default=".",
                help="revision or checkout; default the current checkout",
            )
            s.add_argument(
                "--allow-protected",
                action="store_true",
                help="only with approval; starts a new series",
            )
        s.add_argument(
            "incumbent",
            nargs="?",
            help="default the branch's last accepted commit, or the trunk",
        )
        s.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
        s.add_argument("--seed", type=int, help="default a fresh one")
        s.add_argument("--only", default="", help="workloads whose names hold this")
        s.add_argument(
            "--time",
            type=int,
            metavar="CPU",
            help="also time the x86 images on this idle CPU",
        )
        s.add_argument(
            "--unpinned",
            action="store_true",
            help="run this checkout's evaluator, to work on it; never a promotion",
        )
    s = sub.add_parser("standings")
    s.add_argument("report", nargs="?", type=Path, help="default the newest")
    return p


def pin(unpinned):
    """Re-run from a clean export of the approved evaluator, the trunk's.

    The working tree may be a candidate, and a candidate must not run its own
    judge. What is merged into the trunk is what was approved, so a change to
    scoring is a pull request of its own, and starts a new series in
    ratchet/log.tsv once it is merged.
    """
    if os.environ.get("RATCHET_PINNED") or unpinned:
        return
    held = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", f"{TRUNK}:eval/ratchet.py"],
        cwd=REPO,
        capture_output=True,
    )
    if held.returncode:
        sys.exit(
            f"No approved evaluator: {TRUNK} holds none. Until one is merged, "
            "pass --unpinned to measure with this checkout's"
        )
    commit = git("rev-parse", "--verify", f"{TRUNK}^{{commit}}")
    tree = CACHE / "trees" / commit
    if not tree.exists():
        export(commit, tree)
    # Keep the subcommand: `eval` is also the name of this script's directory.
    command, *rest = sys.argv[1:]
    argv = [command, *(str(Path(a).resolve()) if Path(a).is_dir() else a for a in rest)]
    env = os.environ | {
        "RATCHET_PINNED": "1",
        "RATCHET_REPO": str(REPO.resolve()),
        "RATCHET_EVAL_COMMIT": commit,
        "RATCHET_REPORTS": str(REPORTS.resolve()),
    }
    script = tree / "eval/ratchet.py"
    os.execve(sys.executable, [sys.executable, str(script), *argv], env)


if __name__ == "__main__":
    args = parser().parse_args()
    if args.command == "standings":
        # The newest report of the whole suite, unless one is named.
        whole = len(WORKLOADS) * len(TARGETS) * len(BACKENDS)
        paths = [args.report] if args.report else sorted(REPORTS.glob("*.json"))
        reports = (json.loads(path.read_text()) for path in reversed(paths))
        report = next((r for r in reports if len(r["cells"]) == whole), None)
        if report is None:
            sys.exit(f"no report of the whole suite in {REPORTS}")
        print(standings(report), end="")
        sys.exit(0)
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        sys.exit("the evaluator measures on x86-64 Linux")
    if "WASI_CC" not in os.environ or "SIM65" not in os.environ:
        sys.exit("run in the evaluator's shell: nix develop .#eval, or just eval")
    pin(args.unpinned)
    sys.exit(0 if evaluate(args) else 1)
