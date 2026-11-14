"""Decision boundaries for the x86 experiment. Run with python3 -B test_lab.py."""

import unittest

from lab import compare, verdict_for
from run import stripped


def row(image, times, source=100, size=1000):
    from statistics import median

    return dict(
        elf_sha256=image,
        elf_bytes=size,
        source_gz_bytes=source,
        median_ns=median(times) * 1_000_000,
        median_rss_kib=2048,
        samples=[dict(ns=t * 1_000_000, rss_kib=2048) for t in times],
    )


class Lab(unittest.TestCase):
    def test_identical_code_cannot_win_on_clock_noise(self):
        old = row("same", [100] * 5)
        new = row("same", [60] * 5)
        self.assertEqual(verdict_for(compare(old, new).values()), "no change")
        new["source_gz_bytes"] -= 1
        self.assertEqual(verdict_for(compare(old, new).values()), "improvement")

    def test_one_regression_anywhere_vetoes_other_wins(self):
        base = row("base", [100] * 5)
        quicker = row("quick", [90] * 5)
        larger = row("large", [100] * 5, size=1001)
        changes = [*compare(base, quicker).values(), *compare(base, larger).values()]
        self.assertEqual(verdict_for(changes), "regression")

    def test_mixed_rounds_are_inconclusive_even_with_a_size_win(self):
        base = row("base", [100] * 5)
        mixed = row("mixed", [90, 90, 90, 110, 110], size=999)
        self.assertEqual(verdict_for(compare(base, mixed).values()), "inconclusive")

    def test_hash_inside_a_literal_is_program_source(self):
        literal = 'f -> "${x.or("#one")}"'
        self.assertEqual(stripped(literal + " # comment", "faun"), literal)
        self.assertEqual(stripped("f -> '#' #comment", "faun"), "f -> '#'")


if __name__ == "__main__":
    unittest.main()
