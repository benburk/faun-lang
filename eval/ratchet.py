"""Score a candidate revision of the compiler against the incumbent.

Each side is a checkout directory, built in place, or a git revision, exported
into a cache and built there; no git worktrees are created. Both compile the
suite's programs for every target with the lab backend, favouring speed and
favouring size. A program must print what its C twin prints, and is then
measured beside it: the instructions, fuel or cycles it ran, the memory it
used, and the bytes of its image. Beside the suite are the probes: each a
natural Faun program and its hand-written workaround, its twin, which must
print the same. Probes named `family-spelling` are one computation spelled
several ways, a family, whose spread, its worst spelling over its best, is
scored beside them. See RATCHET.md for the rules.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
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
import resource
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
# and it is the incumbent unless another revision is named.
APPROVED = "origin/main"
TRUNK = os.environ.get("RATCHET_TRUNK", APPROVED)
# The log's series: a protected change, once merged, starts the next one, and
# bumps this with it.
SERIES = 8

X86, WASM, MOS = "x86_64-linux", "wasm32-wasi", "mos6502-sim65"
TARGETS = (X86, WASM, MOS)
# The one backend measured, named on every build.
BACKEND = "lab"
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
# A family's spread on a target and metric, its worst spelling over
# its best, counts in the probes' group as half one spelling's cell: closing
# a gap earns half again what the faster spelling earns, opening one costs
# half what it earns, and slowing the best spelling to close one never pays.
FAMILY = 0.5
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
# A heap takes memory in arenas, each at least as large as the heap so far,
# so whether a buffer fits the last one turns on the size measured: a cell
# whose memory is past the guard is measured again at this part of its size,
# and is past it only where it is there too.
AGAIN = 3 / 4
# A timed program that ran within this part of the incumbent's instructions
# and of its branches, holding the same memory, did the same work: a tenth of
# a percent of the work does not take a tenth longer.
STEADY = 1e-3

SECONDS = 120  # one run's limit
# The most memory one run may hold, so that a program gone wrong fails its
# cell rather than the machine: every program here holds a few megabytes.
MEMORY = 256 << 20
FUEL = 200_000_000_000
CYCLES = 4_000_000_000

GAME = ROOT / "crates/frontend/examples/benchmarks-game"
KERNELS = ROOT / "eval/workloads"
# Outside eval/, so adding one needs no approval; read from the evaluator's
# export, the trunk's, so a branch cannot add one and score itself by it.
PROBES = ROOT / "probes"
PROBE = "probe-"  # what a probe's workload name starts with
# What a spelling's measure is held against in its family: the four each
# target measures. Compiling is one group across targets, and its counts
# vary by a percent, so a spread of them says nothing of a spelling.
SPREAD = ("speed", "memory", "size", "small")


class Workload(NamedTuple):
    """A program in Faun and its C twin, `main.fn` and `main.c` in a folder,
    or a probe: `main.fn`, the natural spelling, and `twin.fn`, the
    workaround, which the incumbent's compiler builds.

    `input` says what a size means: an `argument`; `fasta`, that the C fasta's
    output of that size is standard input; or `bytes`, that so many seeded
    random bytes are. `sizes` holds the size measured on each target: small
    enough to take a fraction of a second, since the counts do not vary. A
    probe runs only on the targets it has a size for.
    """

    name: str
    folder: Path
    input: str
    sizes: dict
    step: int = 1
    libraries: tuple = ()

    @property
    def probe(self):
        return self.name.startswith(PROBE)

    @property
    def home(self):
        """The folder holding the program and its twin."""
        return self.folder / self.name.removeprefix(PROBE)


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
    # Its table is a top-level constant, which the compiler works out again
    # at every use, so a byte costs some two thousand times what it would: these
    # sizes keep that to a fraction of a second, and a fix shows as a gain.
    Workload("crc32", KERNELS, "bytes", sizes(1 << 13, 1 << 11, 16)),
    Workload("collatz", KERNELS, "argument", sizes(20_000, 10_000, 100)),
    Workload("inflate", KERNELS, "argument", sizes(100_000, 30_000, 200)),
    Workload("queens", KERNELS, "argument", sizes(9, 8, 6)),
    Workload("sieve", KERNELS, "argument", sizes(1_000_000, 500_000, 1000)),
    Workload("sort", KERNELS, "argument", sizes(100_000, 30_000, 24)),
]


def probes(folder=PROBES):
    """The probes: each folder under `probes/` holding `main.fn`, `twin.fn`
    and `sizes`, a line for each target it runs on, the target and the size
    its argument is there."""
    found = []
    for listed in sorted(folder.glob("*/sizes")):
        held = {}
        for line in listed.read_text().splitlines():
            if line.strip() and not line.lstrip().startswith("#"):
                target, size = line.split()
                if target not in TARGETS:
                    sys.exit(f"{listed}: no target {target}")
                held[target] = int(size)
        found.append(Workload(PROBE + listed.parent.name, folder, "argument", held))
    for family, members in families(w.name for w in found).items():
        named = {w.name: w for w in found if w.name in members}
        first, *rest = members
        for other in rest:
            if named[other].sizes != named[first].sizes:
                sys.exit(f"family {family}: {other} and {first} differ in sizes")
            twins = (named[name].home / "twin.fn" for name in (other, first))
            if len({path.read_bytes() for path in twins}) > 1:
                sys.exit(f"family {family}: {other} and {first} differ in twins")
    return found


def family(name):
    """The family a probe named `family-spelling` is a spelling of, or `None`
    for a workload of the suite or a probe whose name has no hyphen."""
    if not name.startswith(PROBE):
        return None
    head, hyphen, _ = name.removeprefix(PROBE).partition("-")
    return head if hyphen else None


def families(names):
    """The families among these workloads' names, each the names of its
    spellings, sorted: a family is at least two probes sharing what comes
    before a hyphen. A probe alone with its prefix is a probe like another."""
    found = {}
    for name in sorted(set(names)):
        if family(name):
            found.setdefault(family(name), []).append(name)
    return {k: v for k, v in found.items() if len(v) > 1}


def git(*args, cwd=None):
    return subprocess.check_output(["git", *args], cwd=cwd or REPO, text=True).strip()


def main_checkout():
    return Path(git("rev-parse", "--path-format=absolute", "--git-common-dir")).parent


# Reports live in the main checkout, so they outlast per-idea worktrees.
REPORTS = Path(os.environ.get("RATCHET_REPORTS", main_checkout() / "ratchet/reports"))


def export(commit, dest):
    """Write a commit's tree to dest without creating a worktree."""
    dest.mkdir(parents=True)
    archive = subprocess.Popen(
        ["git", "archive", commit], cwd=REPO, stdout=subprocess.PIPE
    )
    subprocess.run(["tar", "-x", "-C", str(dest)], stdin=archive.stdout, check=True)
    archive.stdout.close()
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
            self.target = None
            self.binary = CACHE / "compilers" / self.commit / "faun"
        self.source = source_of(self.commit) if not self.dirty else None

    def build(self):
        """Build the compiler: a checkout in its own target directory, and a
        revision once, from nothing, in a target directory of its own.

        `git archive` gives every file its commit's time, and cargo judges a
        build fresh by its sources being older than it, so exports sharing a
        target directory took each other's builds: a revision could get a
        compiler built partly from another. A build of its own costs the
        dependencies once per revision, and leaves nothing another
        evaluator running beside this one could be reading."""
        if self.target:
            cargo_build(self.path, self.target)
            return
        if self.binary.exists():
            return
        builds = CACHE / "builds"
        builds.mkdir(parents=True, exist_ok=True)
        target = Path(tempfile.mkdtemp(prefix=f"{self.commit[:12]}-", dir=builds))
        try:
            cargo_build(self.path, target)
            self.binary.parent.mkdir(parents=True, exist_ok=True)
            # Whole or not at all, should another evaluator build it too.
            staged = target / "faun"
            shutil.copy2(target / "release/faun", staged)
            os.replace(staged, self.binary)
        finally:
            shutil.rmtree(target, ignore_errors=True)

    def describe(self):
        return {
            "spec": self.spec,
            "commit": self.commit,
            "dirty": self.dirty,
            "source": self.source,
            "compiler_sha256": sha(self.binary),
        }


def cargo_build(path, target):
    subprocess.run(
        ["cargo", "build", "--locked", "--release", "--quiet", "-p", "faun"],
        cwd=path,
        env=os.environ | {"CARGO_TARGET_DIR": str(target)},
        check=True,
    )


# What the compiler is built from. Not every change here changes the binary,
# a test or a comment, but a change to the binary is a change here.
SOURCES = ("crates", "Cargo.toml", "Cargo.lock", "rust-toolchain.toml")


def source_of(commit):
    """A hash of what a commit builds its compiler from."""
    trees = [
        subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", f"{commit}:{path}"],
            cwd=REPO,
            capture_output=True,
            text=True,
        ).stdout.strip()
        for path in SOURCES
    ]
    return hashlib.sha256(" ".join(trees).encode()).hexdigest()


def same_compiler(incumbent, candidate):
    """Whether two sides' compilers are one file though built from different
    sources: a build taken for another's, unless the change was one the
    binary does not hold, which then measures as no change."""
    built = incumbent["source"] and candidate["source"]
    differ = built and incumbent["source"] != candidate["source"]
    return bool(differ) and incumbent["compiler_sha256"] == candidate["compiler_sha256"]


def protected_changes(candidate, evaluator):
    """Protected paths the candidate changed since its branch left the
    approved evaluator's history."""
    base = git("merge-base", evaluator, candidate.commit)
    against = [candidate.commit] if not candidate.dirty else []
    cwd = candidate.path if candidate.dirty else None
    return git("diff", "--name-only", base, *against, "--", *PROTECTED, cwd=cwd).split()


def probe_changes(candidate, evaluator):
    """Probes the candidate has that differ from the evaluator's, which are
    the ones measured: a new probe lands on the trunk first."""
    against = [candidate.commit] if not candidate.dirty else []
    cwd = candidate.path if candidate.dirty else None
    return git(
        "diff", "--name-only", evaluator, *against, "--", "probes", cwd=cwd
    ).split()


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
        command += [stdin or os.devnull, out, str(FUEL), str(MEMORY), *arguments]
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
                # The 6502 has 64 KiB, and wasm32's linear memory is held by
                # the runtime, whose own reservation is far larger.
                preexec_fn=held_to_memory if target == X86 else None,
            )
        except subprocess.TimeoutExpired:
            return {"status": "timeout"}
    errors = done.stderr.decode(errors="replace")
    code, taken = done.returncode, {}
    if target == X86 and code == 0:
        ns, rss, instructions, cpu, branches = map(int, metrics.read_text().split())
        taken = {"speed": instructions if instructions >= 0 else None}
        taken |= {"memory": rss, "ns": ns, "cpu_ns": cpu}
        taken |= {"branches": branches if branches >= 0 else None}
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


def held_to_memory():
    """Limit what a program and its measurer may map to MEMORY."""
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


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


def c_build(target, workload, directory, reference):
    """The twin's image for a target, or why there is none: cc65 has no
    floats, and there is no GMP for wasm32 or the 6502. A probe's twin is
    Faun, built by the reference side's compiler."""
    if workload.probe:
        image, status, _, _ = faun_build(
            reference, target, False, workload, directory, "twin.fn"
        )
        return image, status
    directory.mkdir(parents=True, exist_ok=True)
    # cl65 leaves its object files beside the source, so compile a copy.
    copy = directory / f"{workload.name}-source"
    shutil.copytree(workload.home, copy)
    command, image = c_command(
        target, workload, copy / "main.c", directory / workload.name
    )
    done = subprocess.run(command, capture_output=True, text=True, timeout=SECONDS)
    if done.returncode:
        return None, first_line(done.stderr)
    return image, "ok"


class Oracle:
    """What each program must print: what its twin, built for this machine,
    prints for the same input. Also makes the inputs. A probe's twin is
    built by the reference side's compiler, the incumbent's."""

    def __init__(self, work, workloads, pool, reference):
        self.work = work / "oracle"
        self.known = {}
        self.reference = reference
        # k-nucleotide reads what the C fasta writes.
        fasta = next(w for w in WORKLOADS if w.name == "fasta")
        needed = {w.name: w for w in [*workloads, fasta]}.values()
        built = pool.map(lambda w: c_build(X86, w, self.work, reference), needed)
        self.images = {}
        for workload, (image, why) in zip(needed, built):
            if image is None:
                sys.exit(f"{workload.name}: the twin does not build: {why}")
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
                sys.exit(f"{workload.name} {size}: the twin: {said['status']}")
            self.known[key] = arguments, stdin, said
        return self.known[key]


def faun_build(side, target, small, workload, directory, file="main.fn"):
    """Build a workload, answering its image or why there is none, and its
    size: for a 6502 image past the machine's 64 KiB, where it would end."""
    directory.mkdir(parents=True, exist_ok=True)
    command = faun_command(side.binary, target, small)
    source = workload.home / file
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
        ns, rss, instructions, _, _ = map(int, metrics.read_text().split())
        taken = {"instructions": instructions, "ns": ns, "rss_kib": rss}
    wrote = re.search(r"^wrote (.+)$", done.stdout, re.M)
    if done.returncode or not wrote:
        past = re.search(r"image ends at \$([0-9A-F]+), past", done.stderr)
        if past:
            return None, "too large", int(past[1], 16), taken
        return None, f"build: {first_line(done.stderr)}", None, taken
    image = Path(wrote[1])
    return image, "ok", image.stat().st_size, taken


def faun_command(binary, target, small):
    """The compiler's command building for a target, the backend named: a
    revision whose default was another backend builds with lab all the same,
    and one whose only backend is lab takes the flag as it is."""
    command = [binary, "build", f"--target={target}", "--backend", BACKEND]
    return command + ["--small"] if small else command


def faun_cell(side, label, target, workload, check, oracle, work):
    """Build a workload both ways for one target, hold both images to the
    oracle at a seeded size, and measure the one built for speed at the
    target's size."""
    directory = work / label / target
    cell = {"status": "ok"}
    images, builds = {}, {}
    for metric, small in (("size", False), ("small", True)):
        image, status, size, builds[metric] = faun_build(
            side, target, small, workload, directory / metric
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
        | {k: said.get(k) for k in ("speed", "memory", "ns", "branches")}
        | {"image": str(image)}
    )


def c_cell(target, workload, oracle, work):
    """The twin's measures on a target, where it builds and agrees there."""
    image, status = c_build(target, workload, work / "c" / target, oracle.reference)
    if image is None:
        return {"status": f"build: {status}"}
    arguments, stdin, expected = oracle.case(workload, workload.sizes[target])
    said = run(target, image, arguments, stdin, image.with_suffix(".out"))
    if said["status"] == "ok" and said["stdout"] != expected["stdout"]:
        said["status"] = "wrong output"
    if said["status"] != "ok":
        return {"status": said["status"]}
    size = small = image.stat().st_size
    if workload.probe:
        # A Faun twin has its own image built `--small`; a C twin's is the one.
        built = faun_build(
            oracle.reference,
            target,
            True,
            workload,
            work / "c" / target / "small",
            "twin.fn",
        )
        small = built[2]
    measures = {k: said.get(k) for k in ("speed", "memory", "ns")}
    return {
        "status": "ok",
        "size": size,
        "small": small,
        "image": str(image),
    } | measures


def timed(cpu, cells, oracle, workloads):
    """Processor times of the x86 images, pinned to one CPU. The sides take
    turns, one run each in turning order, for as many turns as take the
    incumbent a quarter of a second. Whatever else the CPU is doing can only
    lengthen a run, so a side's time is its quickest, kept with its median."""
    allowed = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    for (target, name), sides in cells.items():
        ready = {k: v for k, v in sides.items() if v.get("image")}
        if target != X86 or "candidate" not in ready or "incumbent" not in ready:
            continue
        workload = workloads[name]
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


def same_work(incumbent, candidate):
    """Whether two x86 images ran the same work by every exact count: as
    many instructions and as many branches, within STEADY, and the same
    memory. A time between two such runs is where their code lies, a loop's
    head on one side of a cache line or the other, which a compiler may
    change by changing anything before it."""
    for measure in ("speed", "branches"):
        old, new = incumbent.get(measure), candidate.get(measure)
        if not old or not new or abs(new - old) > old * STEADY:
            return False
    return incumbent.get("memory") == candidate.get("memory")


def again_size(workload, target):
    """The size a cell's memory is measured at again: AGAIN of its own, in
    the workload's steps, and at least one."""
    step = workload.step
    return max(step, int(workload.sizes[target] * AGAIN) // step * step)


def measure_again(cells, oracle, workloads, jobs):
    """Measure again, at the size `again_size` gives, both sides of each
    cell whose memory is past the guard, keeping what each held there."""
    wanted = []
    for (target, name), sides in sorted(cells.items()):
        old, new = sides["incumbent"], sides["candidate"]
        change = ratio(target, "memory", old, new)
        if not isinstance(change, float) or not (old.get("image") and new.get("image")):
            continue
        if beyond(target, "memory", change, old["memory"], new["memory"]):
            wanted.append(((target, name), again_size(workloads[name], target)))
    # Each input is made once, before two cells could ask for it.
    for (target, name), size in wanted:
        oracle.case(workloads[name], size)

    def held(key, size, label):
        target, name = key
        arguments, stdin, expected = oracle.case(workloads[name], size)
        image = Path(cells[key][label]["image"])
        said = run(target, image, arguments, stdin, image.with_suffix(".again"))
        if said["status"] == "ok" and said["stdout"] == expected["stdout"]:
            return said.get("memory")
        return None

    with ThreadPoolExecutor(jobs) as pool:
        found = {
            (key, label): pool.submit(held, key, size, label)
            for key, size in wanted
            for label in ("incumbent", "candidate")
        }
        for key, size in wanted:
            cells[key]["again"] = {"size": size} | {
                label: found[key, label].result()
                for label in ("incumbent", "candidate")
            }


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
    and split it into the gain of the better cells and the loss of the worse.
    Each family's spreads count in the probes' groups beside its spellings,
    each weighing FAMILY of one of their cells."""
    changes, broken = [], []
    for (target, name), sides in sorted(cells.items()):
        for metric in METRICS:
            change = ratio(target, metric, sides["incumbent"], sides["candidate"])
            where = {"target": target, "workload": name, "metric": metric}
            if change == "broken":
                broken.append(where | {"status": sides["candidate"]["status"]})
            elif change is not None:
                old, new = sides["incumbent"].get(metric), sides["candidate"][metric]
                where |= {"ratio": change, "old": old, "new": new}
                if metric == "memory" and "again" in sides:
                    where["again"] = sides["again"]
                changes.append(where)
    widths = spreads(cells)
    groups = {}
    for change in changes:
        groups.setdefault(group(change), []).append((change, 1.0))
    for change in widths:
        groups.setdefault(("probes", change["metric"]), []).append((change, FAMILY))
    total = sum(WEIGHTS[metric] for _, metric in groups) or 1
    gain = loss = 0.0
    for (_, metric), members in groups.items():
        held = sum(weight for _, weight in members)
        for change, weight in members:
            share = WEIGHTS[metric] / total * weight / held * math.log(change["ratio"])
            gain -= min(share, 0.0)
            loss += max(share, 0.0)
    cell_groups = {}
    for change in changes:
        cell_groups.setdefault(group(change), []).append(change)
    return {
        "score": math.exp(loss - gain),
        "gain": gain,
        "loss": loss,
        "groups": {
            f"{target} {metric}": geomean(c["ratio"] for c in members)
            for (target, metric), members in sorted(cell_groups.items())
        },
        "better": sum(c["ratio"] < 1 for c in changes),
        "worse": sum(c["ratio"] > 1 for c in changes),
        "changed": sorted(
            (c for c in changes if c["ratio"] != 1), key=lambda c: c["ratio"]
        ),
        "broken": broken,
        "spreads": widths,
        "spread": {
            metric: geomean(c["ratio"] for c in widths if c["metric"] == metric)
            for metric in SPREAD
            if any(c["metric"] == metric for c in widths)
        },
    }


def spread(target, metric, members, label, steady=False):
    """A family's spread on one side: its worst spelling's measure over its
    best's, with the two spellings' names; `None` where a spelling has no
    measure there. Held `steady`, a measure the same as the incumbent's, by
    the rules a cell's ratio follows, is the incumbent's, so a spread
    changes only where a spelling's measure does."""
    held = {}
    for name, sides in members.items():
        side = sides[label]
        if side.get("status") != "ok" or not side.get(metric):
            return None
        held[name] = side[metric]
        if steady:
            old = sides["incumbent"]
            if old.get("status") != "ok" or not old.get(metric):
                return None
            if ratio(target, metric, old, side) == 1.0:
                held[name] = old[metric]
    best, worst = min(held, key=held.get), max(held, key=held.get)
    return held[worst] / held[best], best, worst


def spreads(cells):
    """Each family's spread on each target and metric its spellings run,
    the candidate's over the incumbent's: below one, the family's spellings
    are nearer each other."""
    found = []
    named = families(name for _, name in cells)
    for target in sorted({t for t, _ in cells}):
        for name, spellings in named.items():
            members = {
                spelling: cells[target, spelling]
                for spelling in spellings
                if (target, spelling) in cells
            }
            if len(members) < 2:
                continue
            for metric in SPREAD:
                old = spread(target, metric, members, "incumbent")
                new = spread(target, metric, members, "candidate", steady=True)
                if old is None or new is None:
                    continue
                found.append(
                    {
                        "target": target,
                        "family": name,
                        "metric": metric,
                        "ratio": 1.0 if new[0] == old[0] else new[0] / old[0],
                        "old": old[0],
                        "new": new[0],
                        "best": new[1].removeprefix(f"{PROBE}{name}-"),
                        "worst": new[2].removeprefix(f"{PROBE}{name}-"),
                    }
                )
    return found


def group(cell):
    """The group a cell's measure counts in. Compiling runs here whatever the
    target, so it is one group. The probes count as one more target does,
    every probe on every target in it, so that many probes do not swamp the
    suite and a fix one of them shows is a gain."""
    if cell["metric"] == "compile":
        return "all", "compile"
    if cell["workload"].startswith(PROBE):
        return "probes", cell["metric"]
    return cell["target"], cell["metric"]


def geomean(ratios):
    logs = [math.log(r) for r in ratios]
    return math.exp(sum(logs) / len(logs)) if logs else None


def beyond(target, metric, change, old, new):
    """Whether a cell's measure is past the guard: more than a tenth worse,
    a compile a quarter, and a memory larger by more than its slack."""
    worst = COMPILE_WORST if metric == "compile" else WORST
    return change > worst and new - old > SLACK.get((target, metric), 0)


def settled(cell):
    """Whether a memory past the guard at its size is not past it at the
    size measured again: where the heap's last arena falls, not what the
    program holds. One not measured again, or not running there, is past."""
    again = cell.get("again") or {}
    old, new = again.get("incumbent"), again.get("candidate")
    if cell["metric"] != "memory" or not old or not new:
        return False
    return not beyond(cell["target"], "memory", new / old, old, new)


def decide(scored, protected=(), slowed=()):
    """The verdict and its reasons, as RATCHET.md states them."""
    reasons = []
    if protected:
        reasons.append("changes protected paths: " + ", ".join(protected))
    for cell in scored["broken"]:
        reasons.append("breaks " + place(cell) + f" ({cell['status']})")
    for cell in scored["changed"]:
        where = cell["target"], cell["metric"], cell["ratio"]
        if beyond(*where, cell["old"], cell["new"]) and not settled(cell):
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


def noted(scored, steady=()):
    """What is reported but rejects nothing: a memory past the guard at its
    size and not at the size measured again, and a timed program taking
    longer though it ran the same work by every count."""
    notes = []
    for cell in scored["changed"]:
        where = cell["target"], cell["metric"], cell["ratio"]
        if beyond(*where, cell["old"], cell["new"]) and settled(cell):
            again = cell["again"]
            notes.append(
                f"{place(cell)} is {cell['ratio'] - 1:.1%} worse but"
                f" {again['candidate'] / again['incumbent'] - 1:+.1%} at"
                f" size {again['size']}"
            )
    for cell in steady:
        notes.append(
            f"{place(cell)} runs {cell['ratio'] - 1:.1%} longer with as many"
            " instructions and branches and the same memory"
        )
    return notes


def place(cell):
    return f"{cell['target']} {cell['workload']} {cell['metric']}"


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
    """Every cell of the suite and the probes for each side, and the twins
    beside them."""
    chosen = [w for w in [*WORKLOADS, *probes()] if only in w.name]
    pool = ThreadPoolExecutor(jobs)
    oracle = Oracle(work, chosen, pool, sides["incumbent"])
    checks = {}
    for workload in chosen:
        for target in workload.sizes:
            # A different size from the one measured, fresh with each seed.
            most = workload.sizes[target] // workload.step
            drawn = random.Random(f"{seed}:{workload.name}:{target}")
            checks[workload.name, target] = workload.step * drawn.randint(
                max(1, most // 3), max(1, most - 1)
            )

    # Each workload's inputs and answers are made once, here, before two of
    # its cells could ask for the same one.
    def cases(workload):
        for target in workload.sizes:
            oracle.case(workload, workload.sizes[target])
            oracle.case(workload, checks[workload.name, target])

    list(pool.map(cases, chosen))
    cells = {}
    with pool:
        for workload in chosen:
            for target in workload.sizes:
                key = target, workload.name
                cells[key] = {"c": pool.submit(c_cell, target, workload, oracle, work)}
                check = checks[workload.name, target]
                for label, side in sides.items():
                    cells[key][label] = pool.submit(
                        faun_cell, side, label, target, workload, check, oracle, work
                    )
        cells = {
            key: {label: pending.result() for label, pending in found.items()}
            for key, found in cells.items()
        }
    return cells, checks, oracle, {w.name: w for w in chosen}


def table(cells, scored):
    """The summary printed after a run: each target's geometric mean change, and how the candidate stands against C; then the same of
    the probes, against their twins; then each family's spread on each
    target, its worst spelling over its best, and how much it changed."""
    lines = []
    for probing, twin in ((False, "x C"), (True, "x twin")):
        heading = "probes" if probing else ""
        lines.append(f"{heading:22}" + "".join(f"{m:>18}" for m in METRICS))
        lines.append(f"{'':22}" + f"{'change':>10}{twin:>8}" * len(METRICS))
        lines += table_rows(cells, probing)
    lines += family_rows(scored["spreads"])
    for cell in scored["changed"][:12] + scored["changed"][12:][-12:]:
        lines.append(f"  {cell['ratio'] - 1:+8.2%}  {place(cell)}")
    moved = sorted(
        (c for c in scored["spreads"] if c["ratio"] != 1), key=lambda c: c["ratio"]
    )
    for change in moved[:6] + moved[6:][-6:]:
        where = f"{change['target']} {change['family']}"
        lines.append(
            f"  {change['ratio'] - 1:+8.2%}  {where} {change['metric']} spread,"
            f" {change['old']:.3g} to {change['new']:.3g}"
        )
    failing = sorted(
        (key, sides["candidate"]["status"])
        for key, sides in cells.items()
        if sides["candidate"]["status"] != "ok"
    )
    for (target, name), status in failing:
        lines.append(f"  not running: {target} {name}: {status}")
    return "\n".join(lines)


def family_rows(widths):
    """A row for each family and target: each metric's spread, the
    candidate's worst spelling over its best, and its change."""
    if not widths:
        return []
    lines = [f"{'families':22}" + "".join(f"{m:>18}" for m in SPREAD)]
    lines.append(f"{'':22}" + f"{'change':>10}{'spread':>8}" * len(SPREAD))
    for name in sorted({c["family"] for c in widths}):
        for target in TARGETS:
            row, seen = f"{name + ' ' + target:22}", False
            for metric in SPREAD:
                held = next(
                    (
                        c
                        for c in widths
                        if (c["family"], c["target"], c["metric"])
                        == (name, target, metric)
                    ),
                    None,
                )
                row += f"{held['ratio'] - 1:>+10.2%}" if held else f"{'-':>10}"
                row += f"{held['new']:>8.2f}" if held else f"{'-':>8}"
                seen = seen or bool(held)
            if seen:
                lines.append(row)
    return lines


def table_rows(cells, probing):
    """A row for each target, of the suite or of the probes."""
    lines = []
    for target in TARGETS:
        row = f"{target:22}"
        for metric in METRICS:
            changes, against = [], []
            for (t, name), sides in cells.items():
                if t != target or name.startswith(PROBE) != probing:
                    continue
                change = ratio(t, metric, sides["incumbent"], sides["candidate"])
                if isinstance(change, float):
                    changes.append(change)
                ours, theirs = sides["candidate"].get(metric), sides["c"].get(metric)
                if sides["candidate"]["status"] == "ok" and ours and theirs:
                    against.append(ours / theirs)
            change, c = geomean(changes), geomean(against)
            row += f"{change - 1:>+10.2%}" if change else f"{'-':>10}"
            row += f"{c:>8.2f}" if c else f"{'-':>8}"
        lines.append(row)
    return lines


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
    each target, and under it what does not run there; then the
    probes' natural spellings against their twins the same way."""
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
        "Under the suite are the probes, each program's natural spelling beside",
        "its workaround in Faun, its twin: there `vs` is the natural spelling's",
        "measure over the twin's, and above one is the compiler's to close.",
        "Last are the families, one computation spelled several natural ways,",
        "each a probe: a spread is the worst spelling's measure over the best's,",
        "and above one is a cliff, the slowest and the largest spelling named.",
    ]
    for probing in (False, True):
        for target in TARGETS:
            lines += standing(report, target, probing)
    for target in TARGETS:
        lines += family_standing(report, target)
    return "\n".join(lines) + "\n"


def family_standing(report, target):
    """One target's table of the families: each metric's spread, the worst
    spelling's measure over the best's, and for speed and memory the worst
    spelling, a cliff to close."""
    cells = {c["workload"]: c for c in report["cells"] if c["target"] == target}
    rows = [["Family", "Speed", "Slowest", "Memory", "Most", "Size", "Small"]]
    for name, spellings in families(cells).items():
        members = {s: cells[s] for s in spellings}
        row = [name]
        for metric in SPREAD:
            found = spread(target, metric, members, "candidate")
            row.append(f"{found[0]:.2f}" if found else "-")
            if metric in ("speed", "memory"):
                worst = found[2].removeprefix(f"{PROBE}{name}-") if found else "-"
                row.append(worst)
        rows.append(row)
    if len(rows) == 1:
        return []
    widths = [max(len(row[at]) for row in rows) for at in range(len(rows[0]))]
    rows.insert(1, ["-" * width for width in widths])
    lines = ["", f"## Families, {target}", ""]
    for row in rows:
        padded = (cell.ljust(width) for cell, width in zip(row, widths))
        lines.append("| " + " | ".join(padded) + " |")
    return lines


def standing(report, target, probing):
    """One target's table of the suite, or of the probes. A table row is held
    to 80 characters, so a probe's columns are headed `vs`, not `vs twin`."""
    lines = []
    cells = [
        c
        for c in report["cells"]
        if c["target"] == target and c["workload"].startswith(PROBE) == probing
    ]
    if not cells:
        return []
    name, twin = ("Probe", "vs") if probing else ("Program", "vs C")
    rows = [[name, "Speed", twin, "Memory", twin, "Size", twin, "Small"]]
    ratios, failing = {"speed": [], "memory": [], "size": []}, []
    for cell in cells:
        ours, c = cell["candidate"], cell["c"]
        if ours["status"] != "ok":
            name = cell["workload"].removeprefix(PROBE)
            failing.append(f"{name}: {ours['status']}")
            continue
        # x86-64 memory is measured in KiB.
        scale = 1024 if target == X86 else 1
        row = [
            cell["workload"].removeprefix(PROBE),
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
    rows.append(mean + [times(means["memory"], 1), "", times(means["size"], 1), ""])
    widths = [max(len(row[at]) for row in rows) for at in range(len(rows[0]))]
    rows.insert(1, ["-" * width for width in widths])
    heading = f"Probes, {target}" if probing else target
    lines += ["", f"## {heading}", ""]
    for row in rows:
        padded = (cell.ljust(width) for cell, width in zip(row, widths))
        lines.append("| " + " | ".join(padded) + " |")
    if failing:
        lines += ["", "Not running:", ""] + [f"- {program}" for program in failing]
    return lines


def evaluate(args):
    kind = "noise" if args.command == "noise" else "eval"
    candidate = Side(args.candidate if kind == "eval" else ".")
    incumbent = Side(args.incumbent or TRUNK)
    if kind == "noise":
        candidate = incumbent
    print(f"incumbent: {incumbent.spec}, {incumbent.commit[:7]}", file=sys.stderr)
    evaluator = os.environ.get("RATCHET_EVAL_COMMIT")
    protected = []
    if evaluator and kind == "eval" and not args.allow_protected:
        protected = protected_changes(candidate, evaluator)
    # Informational: the probes measured are the evaluator's, the trunk's.
    differing = []
    if kind == "eval":
        differing = probe_changes(candidate, evaluator or TRUNK)
    if differing:
        print(
            "warning: the candidate's probes differ from the trunk's, which are"
            " the ones measured; a probe lands on the trunk first: "
            + ", ".join(differing),
            file=sys.stderr,
        )
    for side in {candidate, incumbent}:
        side.build()
    seed = args.seed if args.seed is not None else secrets.randbits(32)
    started = time.time()
    with tempfile.TemporaryDirectory(prefix="faun-ratchet-") as directory:
        work = Path(directory)
        report = {
            # A cell is a program on a target, no longer with a backend.
            "schema": 2,
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
                "family": FAMILY,
                "slower": SLOWER,
                "again": AGAIN,
                "steady": STEADY,
                "memory_limit": MEMORY,
                "backend": BACKEND,
            },
        }
        sides = {"candidate": candidate, "incumbent": incumbent}
        cells, checks, oracle, chosen = measure(sides, seed, args.jobs, args.only, work)
        measure_again(cells, oracle, chosen, args.jobs)
        if args.time is not None:
            timed(args.time, cells, oracle, chosen)
    scored = score(cells)
    slowed, steady = [], []
    for (t, w), sides in sorted(cells.items()):
        old, new = sides["incumbent"], sides["candidate"]
        if slower(old, new):
            cell = {"target": t, "workload": w, "metric": "time"}
            cell["ratio"] = new["time"] / old["time"]
            (steady if same_work(old, new) else slowed).append(cell)
    verdict, reasons = decide(scored, protected, slowed)
    notes = noted(scored, steady)
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
        if same_compiler(report["incumbent"], report["candidate"]):
            caveats.append("the same compiler built from different sources")
    report |= {
        "seconds": round(time.time() - started, 1),
        "timed_cpu": args.time,
        "sizes": {w.name: w.sizes for w in chosen.values()},
        "series": SERIES,
        "probes_differ": differing,
        "checks": {f"{name} {target}": size for (name, target), size in checks.items()},
        "units": {target: dict(zip(METRICS, units)) for target, units in UNITS.items()},
        "cells": [
            {"target": t, "workload": w}
            | {
                label: {k: v for k, v in side.items() if k != "image"}
                for label, side in sides.items()
            }
            for (t, w), sides in sorted(cells.items())
        ],
        "slowed": slowed,
        "steady": steady,
        "verdict": verdict,
        "reasons": reasons,
        "notes": notes,
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
        "noted": notes,
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
    # How far the families' spreads moved, each metric's geometric mean.
    summary["spread"] = {k: round(v, 5) for k, v in scored["spread"].items()}
    print(json.dumps(summary, indent=1))
    row = log_row(summary, idea_of(candidate, args.idea))
    if args.log:
        with (REPO / "ratchet/log.tsv").open("a") as file:
            file.write(row + "\n")
        print("logged to ratchet/log.tsv", file=sys.stderr)
    else:
        print("log row, for --log:", row, sep="\n", file=sys.stderr)
    return verdict == "quiet" or (verdict == "accept" and not caveats)


# The columns of ratchet/log.tsv, as RATCHET.md states them.
LOG = ("series", "idea", "score", *METRICS, "worst", "verdict", "report")


def idea_of(side, given=None):
    """A row's idea: the one given, or the subject of the commit measured,
    which describes the change. Uncommitted changes on top of it are marked,
    since the subject does not describe them."""
    if given:
        return given
    subject = git("log", "-1", "--format=%s", side.commit)
    return f"{subject} (with uncommitted changes)" if side.dirty else subject


def log_row(summary, idea):
    """A run's row of ratchet/log.tsv, in the evaluator's series."""
    verdict, said = summary["verdict"], False
    if summary["reasons"]:
        verdict += ": " + "; ".join(summary["reasons"])
        said = True
    # Reported, rejecting nothing.
    for heading, joined in (("noted", "; "), ("not a promotion", ", ")):
        if summary.get(heading):
            verdict += ";" if said else ":"
            verdict += f" {heading}: " + joined.join(summary[heading])
            said = True
    fields = {"series": str(SERIES), "idea": idea, "verdict": verdict}
    fields["report"] = Path(summary["report"]).name
    for column in ("score", *METRICS, "worst"):
        fields[column] = f"{summary[column]:.5f}"
    return "\t".join(" ".join(fields[column].split()) for column in LOG)


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
            help="default the trunk",
        )
        s.add_argument(
            "--log",
            action="store_true",
            help="append the run's row to ratchet/log.tsv",
        )
        s.add_argument(
            "--idea",
            help="the row's idea; default the measured commit's subject",
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


def positionals(p, argv):
    """Where argv's positional arguments are, the subcommand first: every
    argument that is neither an option nor an option's value."""
    takes = {
        option
        for command in p._subparsers._group_actions[0].choices.values()
        for action in command._actions
        if action.nargs != 0
        for option in action.option_strings
    }
    places, value, ended = [], False, False
    for at, arg in enumerate(argv):
        if value:
            value = False
        elif ended or not arg.startswith("-"):
            places.append(at)
        elif arg == "--":
            ended = True
        else:
            value = "=" not in arg and arg in takes
    return places


def pin(args):
    """Re-run from a clean export of the approved evaluator, the trunk's.

    The working tree may be a candidate, and a candidate must not run its own
    judge. What is merged into the trunk is what was approved, so a change to
    scoring is a pull request of its own, and starts a new series in
    ratchet/log.tsv once it is merged.
    """
    if os.environ.get("RATCHET_PINNED") or args.unpinned:
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
    # Only the candidate and the incumbent may name checkouts; any other
    # argument, such as an idea of any length, is passed on as it is. Skip the
    # subcommand: `eval` is also the name of this script's directory.
    argv = sys.argv[1:]
    sides = [getattr(args, "candidate", None), args.incumbent]
    places = positionals(parser(), argv)
    for at in places[1:]:
        if argv[at] in sides and Path(argv[at]).is_dir():
            argv[at] = str(Path(argv[at]).resolve())
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
        # The newest report of the whole suite and its probes, unless one is
        # named; one from before cells lost their backend is not read.
        whole = {(w.name, t) for w in [*WORKLOADS, *probes()] for t in w.sizes}
        paths = [args.report] if args.report else sorted(REPORTS.glob("*.json"))
        reports = (json.loads(path.read_text()) for path in reversed(paths))
        report = next(
            (
                r
                for r in reports
                if r.get("schema", 1) >= 2
                and whole <= {(c["workload"], c["target"]) for c in r["cells"]}
            ),
            None,
        )
        if report is None:
            sys.exit(f"no report of the whole suite in {REPORTS}")
        print(standings(report), end="")
        sys.exit(0)
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        sys.exit("the evaluator measures on x86-64 Linux")
    if "WASI_CC" not in os.environ or "SIM65" not in os.environ:
        sys.exit("run in the evaluator's shell: nix develop .#eval, or just eval")
    pin(args)
    sys.exit(0 if evaluate(args) else 1)
