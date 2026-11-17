#!/usr/bin/env python3
"""Time the compression libraries against zlib: CRC-32, Adler-32, inflate
of raw, zlib and gzip streams, deflate at levels 1, 6 and 9, and PNG
decoding, each in megabytes a second of the larger side, input for
checksums and deflate, output for inflate and PNG.

Each Faun program reads standard input and writes standard output; its
time is the quickest of `--runs`, less the quickest time of a program that
only reads the same input, so what is left is the library's work. zlib is
Python's, timed on bytes already in memory, its call overhead nothing
beside megabytes. Every Faun answer is checked against zlib's first.

    python3 run.py --cpu 3
    python3 run.py --cpu 3 --only inflate --faun target/release/faun

The inputs are made from the flate fixtures, committed bytes, so they are
the same at every commit: the 70 KB text repeated, whose repeats lie
further apart than DEFLATE's window reaches, random bytes from a seed, and
an image whose rows take each PNG filter in turn."""

import argparse
import os
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import time
import zlib

HERE = Path(__file__).resolve().parent
LIBRARIES = HERE.parent.parent
REPOSITORY = LIBRARIES.parent.parent.parent.parent

MB = 1_000_000


def corpus(size):
    """The fixture text repeated to `size` bytes."""
    text = (LIBRARIES / "flate/fixtures/input/text").read_bytes()
    return (text * (size // len(text) + 1))[:size]


def png_chunk(kind, data):
    body = kind + data
    return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body))


def image(width, height):
    """An 8-bit RGBA PNG: smooth gradients with a little noise, as a photo
    has, its rows filtered None, Sub, Up, Average and Paeth in turn, and
    its pixels as 8-bit RGBA."""
    rng = random.Random(23)
    stride = width * 4
    rows = []
    for y in range(height):
        rows.append(
            bytes(
                (
                    (x * 3 + y) // 4 + rng.randrange(8),
                    (x + y * 2) // 6 + rng.randrange(8),
                    (x * y) // (width * 8) + rng.randrange(8),
                    255 - rng.randrange(4),
                )[i]
                & 255
                for x in range(width)
                for i in range(4)
            )
        )
    filtered = bytearray()
    previous = bytes(stride)
    for y, row in enumerate(rows):
        kind = y % 5
        filtered.append(kind)
        for i in range(stride):
            a = row[i - 4] if i >= 4 else 0
            b = previous[i]
            c = previous[i - 4] if i >= 4 else 0
            if kind == 0:
                guess = 0
            elif kind == 1:
                guess = a
            elif kind == 2:
                guess = b
            elif kind == 3:
                guess = (a + b) // 2
            else:
                p = a + b - c
                pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
                guess = a if pa <= pb and pa <= pc else b if pb <= pc else c
            filtered.append((row[i] - guess) & 255)
        previous = row
    header = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)
    data = zlib.compress(bytes(filtered), 6)
    png = (
        b"\x89PNG\r\n\x1a\n"
        + png_chunk(b"IHDR", header)
        + png_chunk(b"IDAT", data)
        + png_chunk(b"IEND", b"")
    )
    return png, b"".join(rows), data


def pam(width, height, pixels):
    return (
        f"P7\nWIDTH {width}\nHEIGHT {height}\nDEPTH 4\nMAXVAL 255\n"
        "TUPLTYPE RGB_ALPHA\nENDHDR\n"
    ).encode() + pixels


def quickest(command, stdin_path, runs, expected):
    best = None
    for _ in range(runs):
        with open(stdin_path, "rb") as stdin:
            start = time.perf_counter()
            result = subprocess.run(command, stdin=stdin, capture_output=True)
            elapsed = time.perf_counter() - start
        if result.returncode != 0 or (
            expected is not None and result.stdout != expected
        ):
            raise SystemExit(
                f"{' '.join(map(str, command))}: wrong answer, status {result.returncode}"
            )
        best = elapsed if best is None else min(best, elapsed)
    return best


def zlib_time(work, runs):
    best = None
    for _ in range(runs):
        start = time.perf_counter()
        work()
        elapsed = time.perf_counter() - start
        best = elapsed if best is None else min(best, elapsed)
    return best


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--cpu", type=int, help="an idle CPU to run pinned to")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--size", type=int, default=16, help="megabytes of text")
    parser.add_argument("--width", type=int, default=1024, help="the image's side")
    parser.add_argument("--only", default="", help="rows whose names hold this")
    parser.add_argument(
        "--faun", default=str(REPOSITORY / "target/release/faun"), help="the compiler"
    )
    args = parser.parse_args()
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    with tempfile.TemporaryDirectory(prefix="faun-flate-bench-") as directory:
        work = Path(directory)
        programs = {
            "length": HERE / "length.fn",
            "checksum": HERE / "checksum.fn",
            "gzip": LIBRARIES / "flate/examples/gzip.fn",
            "topam": LIBRARIES / "png/examples/topam.fn",
        }
        built = {}
        for name, source in programs.items():
            built[name] = work / name
            subprocess.run(
                [args.faun, "build", str(source), "-o", str(built[name])],
                check=True,
                stdout=subprocess.DEVNULL,
            )

        text = corpus(args.size * MB)
        noise = random.Random(19).randbytes(args.size * MB // 4)
        png, pixels, idat = image(args.width, args.width)
        files = {}
        streams = {}

        def file(name, data):
            files[name] = work / name
            files[name].write_bytes(data)
            streams[name] = data
            return files[name]

        file("text", text)
        file("noise", noise)
        raw = zlib.compressobj(6, zlib.DEFLATED, -15)
        file("text.raw", raw.compress(text) + raw.flush())
        file("text.zlib", zlib.compress(text, 6))
        gz = zlib.compressobj(6, zlib.DEFLATED, 31)
        file("text.gz", gz.compress(text) + gz.flush())
        file("image.png", png)

        def deflated(level):
            def work():
                stream = zlib.compressobj(level, zlib.DEFLATED, 31)
                return stream.compress(text) + stream.flush()

            return work

        # Each row: its name, the program and its arguments, its input, the
        # megabytes it is measured by, what it must print or nothing where
        # its output is checked by reading it back, and zlib's work.
        rows = [
            (
                "crc32",
                ["checksum", "crc32"],
                "text",
                len(text),
                f"{zlib.crc32(text)}\n".encode(),
                lambda: zlib.crc32(text),
            ),
            (
                "adler32",
                ["checksum", "adler32"],
                "text",
                len(text),
                f"{zlib.adler32(text)}\n".encode(),
                lambda: zlib.adler32(text),
            ),
            (
                "inflate raw",
                ["gzip", "-d", "--raw"],
                "text.raw",
                len(text),
                text,
                lambda: zlib.decompress(streams["text.raw"], -15),
            ),
            (
                "inflate zlib",
                ["gzip", "-d", "--zlib"],
                "text.zlib",
                len(text),
                text,
                lambda: zlib.decompress(streams["text.zlib"]),
            ),
            (
                "inflate gzip",
                ["gzip", "-d"],
                "text.gz",
                len(text),
                text,
                lambda: zlib.decompress(streams["text.gz"], 31),
            ),
            (
                "inflate noise",
                ["gzip", "-d", "--raw"],
                "noise.raw",
                len(noise),
                noise,
                lambda: zlib.decompress(streams["noise.raw"], -15),
            ),
            ("deflate 1", ["gzip", "-1"], "text", len(text), None, deflated(1)),
            ("deflate 6", ["gzip", "-6"], "text", len(text), None, deflated(6)),
            ("deflate 9", ["gzip", "-9"], "text", len(text), None, deflated(9)),
            (
                "png decode",
                ["topam"],
                "image.png",
                len(pixels),
                pam(args.width, args.width, pixels),
                lambda: zlib.decompress(idat),
            ),
        ]
        stored = zlib.compressobj(6, zlib.DEFLATED, -15)
        file("noise.raw", stored.compress(noise) + stored.flush())
        width = max(len(row[0]) for row in rows)
        print(
            f"{'':{width}}  {'Faun MB/s':>10}  {'zlib MB/s':>10}  {'ratio':>6}  sizes"
        )
        reading = {}
        for name, command, input_name, size, expected, reference in rows:
            if args.only not in name:
                continue
            stdin_path = files[input_name]
            if input_name not in reading:
                reading[input_name] = quickest(
                    [built["length"]], stdin_path, args.runs, None
                )
            program = [built[command[0]], *command[1:]]
            seconds = quickest(program, stdin_path, args.runs, expected)
            work_seconds = max(seconds - reading[input_name], 1e-6)
            faun = size / MB / work_seconds
            note = ""
            if expected is None:
                with open(stdin_path, "rb") as stdin:
                    ours = subprocess.run(
                        program, stdin=stdin, capture_output=True
                    ).stdout
                if zlib.decompress(ours, 31) != text:
                    raise SystemExit(f"{name}: does not read back")
                note = f"{len(ours):,} against {len(reference()):,}"
            zlib_mbs = (
                size / MB / zlib_time(reference, args.runs) if reference else None
            )
            shown = f"{zlib_mbs:10.0f}" if zlib_mbs else f"{'':>10}"
            ratio = f"{zlib_mbs / faun:5.1f}x" if zlib_mbs else ""
            print(
                f"{name:{width}}  {faun:10.1f}  {shown}  {ratio:>6}  {note}", flush=True
            )


if __name__ == "__main__":
    sys.exit(main())
