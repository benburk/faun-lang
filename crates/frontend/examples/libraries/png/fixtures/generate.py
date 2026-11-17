"""Writes expected.txt: for every image of PngSuite, its size and the
CRC-32 of its pixels as 8-bit red, green, blue and alpha, worked out by
pypng, a decoder written apart from this one; or `error` for the files
PngSuite marks corrupt, their names starting with `x`.

The pixels follow png.fn's conventions: a 16-bit sample keeps its high
byte, a narrower one is scaled so its largest value is 255, and only tRNS
makes a pixel transparent. Run it with pypng installed, from anywhere:

    nix shell --impure --expr \
      'with import <nixpkgs> {}; python3.withPackages (p: [p.pypng p.pillow])' \
      -c python3 -I generate.py

With Pillow there too, every 8-bit image without tRNS is checked against
Pillow's decoding as well.
"""

import pathlib
import zlib

import png

here = pathlib.Path(__file__).resolve().parent
suite = here / "pngsuite"


def scaled(value, depth):
    if depth == 16:
        return value >> 8
    return value * 255 // ((1 << depth) - 1)


def rgba(path):
    reader = png.Reader(filename=str(path))
    width, height, rows, info = reader.read()
    depth = info["bitdepth"]
    planes = info["planes"]
    # pypng gives the key as a tuple of samples, one for grey.
    key = info.get("transparent")
    palette = reader.palette(alpha="force") if reader.color_type == 3 else None
    out = bytearray()
    for row in rows:
        row = list(row)
        for x in range(width):
            samples = row[x * planes : (x + 1) * planes]
            if palette is not None:
                index = samples[0]
                out += (
                    bytes(palette[index])
                    if index < len(palette)
                    else bytes([0, 0, 0, 255])
                )
            elif planes in (1, 3):
                levels = [scaled(s, depth) for s in samples]
                if planes == 1:
                    levels *= 3
                hidden = key is not None and tuple(samples) == tuple(key)
                out += bytes(levels + [0 if hidden else 255])
            else:
                levels = [scaled(s, depth) for s in samples]
                if planes == 2:
                    levels = [levels[0]] * 3 + [levels[1]]
                out += bytes(levels)
    return width, height, bytes(out), info


def pillow_check(path, width, height, pixels, info):
    try:
        from PIL import Image
    except ImportError:
        return
    if info["bitdepth"] != 8 or "transparent" in info:
        return
    image = Image.open(path)
    if "transparency" in image.info:
        return
    assert image.convert("RGBA").tobytes() == pixels, path.name


def main():
    lines = []
    for path in sorted(suite.glob("*.png")):
        if path.name.startswith("x"):
            lines.append(f"{path.name} error")
            continue
        width, height, pixels, info = rgba(path)
        pillow_check(path, width, height, pixels, info)
        lines.append(f"{path.name} {width} {height} {zlib.crc32(pixels):08x}")
    (here / "expected.txt").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
