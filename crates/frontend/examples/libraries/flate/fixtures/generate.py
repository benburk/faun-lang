"""Write the inflate fixtures: each input, and each input compressed by
Python's zlib as raw DEFLATE, a zlib stream and a gzip file.

Run from anywhere with `python3 -I generate.py`; it writes beside itself.
The inputs are fixed by their seeds, so running it again changes nothing
unless zlib compresses differently.
"""

import gzip
import random
import shutil
import struct
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORDS = (
    "the of and to in is that for it as was with be by on not he this are or "
    "his from at which but have an they you were her she there been one all "
    "would their we him when who more no if out so said what up its about "
    "into than them can only other new some could time these two may then do "
    "first any my now such like our over man me even most made after also "
    "deflate huffman window length distance literal block stored fixed "
    "dynamic checksum adler crc zlib gzip faun buffer bit byte"
).split()


def text(size, seed):
    """Words and punctuation, as prose repeats itself."""
    rng = random.Random(seed)
    out = []
    length = 0
    while length < size:
        word = rng.choice(WORDS)
        if rng.random() < 0.08:
            word += rng.choice([".", ",", ";", "\n"])
        out.append(word)
        length += len(word) + 1
    return " ".join(out).encode()[:size]


def inputs():
    rng = random.Random(1951)
    return {
        "empty": b"",
        "one": b"x",
        "repetitive": b"abcdefgh" * 1000 + b"a" * 60000,
        "text": text(70000, 1950),
        "random": bytes(rng.getrandbits(8) for _ in range(70000)),
    }


def raw(data, level, strategy=zlib.Z_DEFAULT_STRATEGY):
    c = zlib.compressobj(level, zlib.DEFLATED, -15, 9, strategy)
    return c.compress(data) + c.flush()


def gzip_with_header(data):
    """A gzip member with every optional header field: extra, name, comment
    and a header CRC."""
    flags = 2 | 4 | 8 | 16
    header = b"\x1f\x8b\x08" + bytes([flags]) + struct.pack("<I", 0) + b"\x00\xff"
    extra = b"AB\x02\x00hi"
    header += struct.pack("<H", len(extra)) + extra + b"name.txt\x00" + b"a comment\x00"
    header += struct.pack("<H", zlib.crc32(header) & 0xFFFF)
    trailer = struct.pack("<II", zlib.crc32(data), len(data) & 0xFFFFFFFF)
    return header + raw(data, 6) + trailer


def main():
    for old in ("input", "deflate"):
        shutil.rmtree(HERE / old, ignore_errors=True)
        (HERE / old).mkdir()
    for name, data in inputs().items():
        (HERE / "input" / name).write_bytes(data)
        out = HERE / "deflate"
        # Every level as gzip; raw and zlib at the levels where zlib's
        # strategy changes, and stored only where it is small. Random data
        # compresses to itself, so two levels show it all.
        for level in [0, 6] if name == "random" else range(10):
            (out / f"{name}.{level}.gz").write_bytes(
                gzip.compress(data, level, mtime=0)
            )
        for level in [6] if name == "random" else [0, 1, 6, 9]:
            if level == 0 and len(data) > 1000:
                continue
            (out / f"{name}.{level}.raw").write_bytes(raw(data, level))
            (out / f"{name}.{level}.zlib").write_bytes(zlib.compress(data, level))
    data = inputs()["text"]
    out = HERE / "deflate"
    for strategy, label in [
        (zlib.Z_FIXED, "fixed"),
        (zlib.Z_HUFFMAN_ONLY, "huffman"),
        (zlib.Z_RLE, "rle"),
        (zlib.Z_FILTERED, "filtered"),
    ]:
        (out / f"text.{label}.raw").write_bytes(raw(data, 6, strategy))
    (out / "text.header.gz").write_bytes(gzip_with_header(data))
    (out / "text.members.gz").write_bytes(
        gzip.compress(data[:30000], 6, mtime=0)
        + gzip.compress(data[30000:], 9, mtime=0)
    )


main()
