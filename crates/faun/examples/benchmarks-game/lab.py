"""Compare release builds of the same x86-64 Linux programs with fixed C references.

Run this from the trusted prep checkout. Each Faun tree supplies its own
main.fn and compiler. The verifier supplies everything else. See LAB.md.
"""

import argparse
import datetime
import hashlib
import json
import os
import platform
import random
import shutil
import statistics
import subprocess
import struct
import tempfile
from pathlib import Path

from run import BENCHMARKS, C_FLAGS, C_LIBRARIES, HERE, REPOSITORY, gz_size

SUITE = HERE.relative_to(REPOSITORY)
METRICS = ("elf_bytes", "source_gz_bytes", "median_ns", "median_rss_kib")
# Differential checks stay cheap, vary with the seed, and avoid pidigits'
# C reference's missing last line at nonmultiples of ten.
EXTRA = {
    "binary-trees": range(7, 13),
    "fannkuch-redux": range(4, 7),
    "fasta": range(401, 800),
    "k-nucleotide": range(1200, 1800),
    "mandelbrot": range(51, 91),
    "n-body": range(41, 301),
    "pidigits": range(30, 151, 10),
    "spectral-norm": range(11, 51),
}


def sha(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def git(tree, *args):
    return subprocess.check_output(["git", "-C", tree, *args], text=True).strip()


def revision(tree):
    return {
        "commit": git(tree, "rev-parse", "HEAD"),
        "dirty": bool(git(tree, "status", "--porcelain")),
    }


def measure(probe, image, args, stdin, output, limit):
    metrics = probe.with_name("metrics")
    with (stdin or Path(os.devnull)).open("rb") as src, output.open("wb") as dst:
        run = subprocess.run(
            [probe, str(limit), metrics, image, *args],
            stdin=src,
            stdout=dst,
            stderr=subprocess.PIPE,
        )
    if run.returncode:
        raise SystemExit(
            f"{image.name} {args}: exit {run.returncode}: {run.stderr[:300]!r}"
        )
    if run.stderr:
        raise SystemExit(
            f"{image.name} {args}: unexpected stderr: {run.stderr[:300]!r}"
        )
    ns, rss = map(int, metrics.read_text().split())
    return {"ns": ns, "rss_kib": rss}


def check_faun_elf(image):
    # A script delegating to C, or a tiny launcher importing its payload
    # through a shared object, is not a smaller standalone Faun program.
    data = image.read_bytes()
    if (
        len(data) < 64
        or data[:6] != b"\x7fELF\x02\x01"
        or struct.unpack_from("<H", data, 18)[0] != 62
    ):
        raise SystemExit(f"{image}: expected an x86-64 ELF executable")
    (offset,) = struct.unpack_from("<Q", data, 32)
    stride, count = struct.unpack_from("<HH", data, 54)
    if stride < 56 or not count or offset + count * stride > len(data):
        raise SystemExit(f"{image}: invalid ELF program header table")
    types = [
        struct.unpack_from("<I", data, offset + i * stride)[0] for i in range(count)
    ]
    if 1 not in types or 3 in types:
        raise SystemExit(f"{image}: expected a standalone ELF without an interpreter")


def c_build(cc, name, image):
    subprocess.run(
        [
            cc,
            *C_FLAGS,
            "-s",
            HERE / name / "main.c",
            "-o",
            image,
            "-lm",
            *C_LIBRARIES.get(name, []),
        ],
        check=True,
        timeout=120,
    )


def check_output(probe, image, case, output, expected, limit):
    args, stdin = case
    sample = measure(probe, image, args, stdin, output, limit)
    actual = sha(output)
    if expected is not None and actual != expected:
        raise SystemExit(
            f"{image.name} {args}: stdout {actual} differs from expected {expected}"
        )
    return actual, sample


def compare(old, new):
    """Exact sizes; paired timing and RSS with floors for measurement noise."""
    changes = {}
    for metric in METRICS:
        a, b = old[metric], new[metric]
        if metric in ("elf_bytes", "source_gz_bytes"):
            changes[metric] = "better" if b < a else "worse" if b > a else "flat"
        elif old["elf_sha256"] == new["elf_sha256"]:
            changes[metric] = "flat"
        else:
            key = "ns" if metric == "median_ns" else "rss_kib"
            floor = 1_000_000 if key == "ns" else 128
            band = max(floor, 0.05 * a)
            if abs(b - a) <= band:
                changes[metric] = "flat"
                continue
            direction = 1 if b > a else -1
            votes = sum(
                direction * (y[key] - x[key]) > 0
                for x, y in zip(old["samples"], new["samples"], strict=True)
            )
            changes[metric] = (
                ("worse" if direction == 1 else "better")
                if votes * 5 >= 4 * len(old["samples"])
                else "uncertain"
            )
    return changes


def verdict_for(changes):
    if "worse" in changes:
        return "regression"
    if "uncertain" in changes:
        return "inconclusive"
    if "better" in changes:
        return "improvement"
    return "no change"


def benchmark(work, args, compilers, name, checked, size, fasta):
    print(f"{name} (n={size})", flush=True)
    probe, output = work / "probe", work / "stdout"
    images = {"c": work / f"{name}-c"}
    c_build(args.cc, name, images["c"])
    rows = {}
    for side, (tree, compiler, backend) in compilers.items():
        # Only main.fn counts as program source. Compiling from an empty
        # package prevents hiding a benchmark-specific helper in another file.
        folder = work / side / name
        folder.mkdir(parents=True)
        src = folder / "main.fn"
        shutil.copyfile(tree / SUITE / name / "main.fn", src)
        image = work / f"{name}-{side}"
        cmd = [compiler, "build", "--target=x86_64-linux"]
        if backend:
            cmd.append(f"--backend={backend}")
        subprocess.run(
            [*cmd, src, "-o", image],
            env={**os.environ, "FAUN_STD": str(REPOSITORY / "crates/faun/standard")},
            check=True,
            timeout=120,
            stdout=subprocess.DEVNULL,
        )
        check_faun_elf(image)
        images[side] = image
        rows[side] = {
            "source_gz_bytes": gz_size(src, "faun"),
            "source_sha256": sha(src),
        }
    src = HERE / name / "main.c"
    rows["c"] = {"source_gz_bytes": gz_size(src, "c"), "source_sha256": sha(src)}
    for side, image in images.items():
        rows[side].update(
            elf_bytes=image.stat().st_size, elf_sha256=sha(image), samples=[]
        )

    inputs = {}

    def case(n):
        if name != "k-nucleotide":
            return [str(n)], None
        if n not in inputs:
            if n == checked:
                inputs[n] = HERE / "fasta" / f"{checked}.out"
            else:
                inputs[n] = work / f"input-{n}"
                measure(probe, fasta, [str(n)], None, inputs[n], args.timeout)
        return [], inputs[n]

    golden = sha(HERE / name / f"{checked}.out")
    for side, image in images.items():
        if name != "pidigits" or side != "c":
            check_output(probe, image, case(checked), output, golden, args.timeout)
    extra = random.Random(f"{name}:{args.seed}").choice(EXTRA[name])
    checks = []
    for n in (extra, size):
        args_stdin = case(n)
        expected, _ = check_output(
            probe, images["c"], args_stdin, output, None, args.timeout
        )
        for side in compilers:
            check_output(
                probe, images[side], args_stdin, output, expected, args.timeout
            )
        checks.append(
            {
                "size": n,
                "stdout_sha256": expected,
                "stdin_sha256": sha(args_stdin[1]) if args_stdin[1] else None,
            }
        )
    # The measured-size check above also warms each executable. Rotate who
    # runs first, and pair samples by round. Hashing is outside the clock.
    sides = list(images)
    for trial in range(args.runs):
        at = trial % len(sides)
        for side in sides[at:] + sides[:at]:
            _, sample = check_output(
                probe, images[side], args_stdin, output, expected, args.timeout
            )
            rows[side]["samples"].append(sample)
    for side, row in rows.items():
        row["median_ns"] = statistics.median(s["ns"] for s in row["samples"])
        row["median_rss_kib"] = statistics.median(s["rss_kib"] for s in row["samples"])
        print(
            f"  {side:10} {row['median_ns'] / 1e6:9.2f} ms  {row['median_rss_kib']:8g} KiB  {row['elf_bytes']:7} ELF B  {row['source_gz_bytes']:4} source.gz B",
            flush=True,
        )
    for side in compilers:
        rows[side]["ratio_to_c"] = {
            m: rows[side][m] / rows["c"][m] if rows["c"][m] else None for m in METRICS
        }
    result = {"size": size, "golden_sha256": golden, "checks": checks, "rows": rows}
    if "candidate" in rows:
        result["change"] = compare(rows["baseline"], rows["candidate"])
        print(
            "  vs baseline:",
            ", ".join(f"{k}: {v}" for k, v in result["change"].items()),
        )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", required=True, type=int, help="an idle Linux CPU")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument(
        "--timeout", type=int, default=600, help="seconds per execution"
    )
    parser.add_argument("--only", choices=[b[0] for b in BENCHMARKS])
    parser.add_argument("--game", action="store_true")
    parser.add_argument("--cc", default="gcc")
    parser.add_argument(
        "--json", type=Path, required=True, help="new report (never overwrite)"
    )
    parser.add_argument(
        "--gate",
        action="store_true",
        help="require all eight default workloads and a Pareto improvement",
    )
    for side in ("baseline", "candidate"):
        parser.add_argument(
            f"--{side}-tree",
            type=Path,
            default=REPOSITORY if side == "baseline" else None,
        )
        parser.add_argument(
            f"--{side}-bin", type=Path, help="default: TREE/target/release/faun"
        )
        parser.add_argument(
            f"--{side}-backend", help="optional name for faun build --backend"
        )
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("requires native x86-64 Linux")
    if args.cpu not in os.sched_getaffinity(0) or min(args.runs, args.timeout) < 1:
        parser.error("supply an allowed CPU and positive run count and timeout")
    if args.gate and (
        args.only or args.game or args.runs < 5 or not args.candidate_tree
    ):
        parser.error(
            "--gate needs a candidate and all default workloads with at least five rounds"
        )
    if args.json.exists():
        parser.error(f"{args.json} exists; choose a new report")
    if (args.candidate_bin or args.candidate_backend) and not args.candidate_tree:
        parser.error("choose the candidate source tree with --candidate-tree")
    os.sched_setaffinity(0, {args.cpu})
    compilers, provenance = {}, {}
    for side in ("baseline", "candidate"):
        tree = getattr(args, f"{side}_tree")
        if tree is not None:
            tree = tree.resolve()
            binary = (
                getattr(args, f"{side}_bin") or tree / "target/release/faun"
            ).resolve()
            if not binary.is_file() or not os.access(binary, os.X_OK):
                parser.error(f"build the release compiler first: {binary}")
            backend = getattr(args, f"{side}_backend")
            compilers[side] = tree, binary, backend
            provenance[side] = {
                **revision(tree),
                "tree": str(tree),
                "binary": str(binary),
                "compiler_sha256": sha(binary),
                "backend": backend or "default",
            }
    report = {
        "schema": 1,
        "started_utc": datetime.datetime.now(datetime.UTC).isoformat(),
        "flake_lock_sha256": sha(REPOSITORY / "flake.lock"),
        "verifier": revision(REPOSITORY),
        "compilers": provenance,
        "kernel": platform.release(),
        "cpu_model": next(
            s.split(":", 1)[1].strip()
            for s in Path("/proc/cpuinfo").read_text().splitlines()
            if s.startswith("model name")
        ),
        "cpu": args.cpu,
        "runs": args.runs,
        "seed": args.seed,
        "timeout_s": args.timeout,
        "profile": "game" if args.game else "default",
        "cc": shutil.which(args.cc),
        "cc_version": subprocess.check_output(
            [args.cc, "--version"], text=True
        ).splitlines()[0],
        "c_flags": [*C_FLAGS, "-s"],
        "c_libraries": {"all": ["-lm"], **C_LIBRARIES},
        "python": platform.python_version(),
        "benchmarks": {},
    }
    if args.gate and (
        report["verifier"]["dirty"] or any(p["dirty"] for p in provenance.values())
    ):
        parser.error("--gate requires clean verifier, baseline and candidate checkouts")
    with tempfile.TemporaryDirectory(prefix="faun-codegen-") as directory:
        work = Path(directory)
        subprocess.run(
            [args.cc, "-O2", HERE / "measure.c", "-o", work / "probe"], check=True
        )
        fasta = work / "input-generator"
        if args.only in (None, "k-nucleotide"):
            c_build(args.cc, "fasta", fasta)
        for name, checked, game, default in BENCHMARKS:
            if args.only in (None, name):
                report["benchmarks"][name] = benchmark(
                    work,
                    args,
                    compilers,
                    name,
                    checked,
                    game if args.game else default,
                    fasta,
                )
    verdict = "baseline"
    if args.candidate_tree:
        changes = {
            change
            for result in report["benchmarks"].values()
            for change in result["change"].values()
        }
        verdict = verdict_for(changes)
    report["verdict"] = verdict
    report["gate_passed"] = args.gate and verdict == "improvement"
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with args.json.open("x") as out:
        json.dump(report, out, indent=2)
        out.write("\n")
    print(f"{verdict}: {args.json}")
    if args.gate and not report["gate_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
