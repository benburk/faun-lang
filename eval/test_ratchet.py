"""Decision boundaries of the ratchet. Run with python3 -B test_ratchet.py."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import ratchet
from ratchet import (
    LOG,
    MOS,
    WASM,
    X86,
    decide,
    log_row,
    parser,
    ratio,
    score,
    same_compiler,
    slower,
)


def cell(
    speed=1000,
    memory=100,
    size=5000,
    small=4000,
    image="one",
    status="ok",
    compile=None,
):
    return dict(
        status=status,
        speed=speed,
        memory=memory,
        size=size,
        small=small,
        size_sha256=image,
        compile=compile,
    )


def suite(candidates, incumbents=None, target=WASM):
    """Cells of one target and backend, a workload for each candidate."""
    incumbents = incumbents or [cell() for _ in candidates]
    return {
        (target, "stock", f"program-{at}"): {"incumbent": old, "candidate": new}
        for at, (old, new) in enumerate(zip(incumbents, candidates, strict=True))
    }


def verdict(cells, **guards):
    return decide(score(cells), **guards)[0]


class Ratchet(unittest.TestCase):
    def test_the_same_measures_are_no_change(self):
        self.assertEqual(verdict(suite([cell(), cell()])), "no change")

    def test_a_gain_with_no_loss_is_accepted(self):
        smaller = cell(size=4900, image="two")
        self.assertEqual(verdict(suite([smaller, cell()])), "accept")

    def test_a_gain_too_small_to_matter_is_neutral(self):
        smaller = cell(size=4999, image="two")
        self.assertEqual(verdict(suite([smaller, cell()])), "neutral")

    def test_compiling_is_one_group_whatever_the_target(self):
        cells = suite([cell(compile=1000)], [cell(compile=1000)], X86)
        cells |= suite([cell(compile=500)], [cell(compile=1000)], MOS)
        scored = score(cells)
        self.assertIn("all compile", scored["groups"])
        self.assertNotIn("x86_64-linux compile", scored["groups"])
        self.assertAlmostEqual(scored["groups"]["all compile"], 0.5**0.5)

    def test_compile_counts_within_their_jitter_are_the_same(self):
        self.assertEqual(
            ratio(X86, "compile", cell(compile=1000), cell(compile=1019)), 1.0
        )
        self.assertGreater(
            ratio(MOS, "compile", cell(compile=1000), cell(compile=1021)), 1.0
        )

    def test_compiling_may_cost_a_quarter_more_before_it_rejects(self):
        quicker = cell(speed=100, memory=10, image="quick", compile=1000)
        heavier = cell(compile=1240)
        same = [cell(compile=1000), cell(compile=1000)]
        self.assertEqual(verdict(suite([quicker, heavier], same)), "accept")
        heaviest = cell(compile=1260)
        self.assertEqual(verdict(suite([quicker, heaviest], same)), "reject")

    def test_a_small_loss_is_paid_for_by_a_gain_twice_its_size(self):
        quicker = cell(speed=850, image="quick")
        larger = cell(size=5200, image="large")
        self.assertEqual(verdict(suite([quicker, larger])), "accept")
        much_larger = cell(size=5490, image="large")
        self.assertEqual(verdict(suite([quicker, much_larger])), "reject")

    def test_no_gain_pays_for_a_cell_more_than_a_tenth_worse(self):
        quicker = cell(speed=100, memory=10, image="quick")
        slower_ = cell(speed=1101, image="slow")
        self.assertEqual(verdict(suite([quicker, quicker, slower_])), "reject")
        within = cell(speed=1099, image="slow")
        self.assertEqual(verdict(suite([quicker, quicker, within])), "accept")

    def test_a_little_more_memory_is_not_past_the_tenth(self):
        quicker = cell(speed=100, image="quick")
        pages = cell(memory=116, image="pages")
        self.assertEqual(verdict(suite([quicker, pages], target=X86)), "accept")
        more = cell(memory=117, image="pages")
        self.assertEqual(verdict(suite([quicker, more], target=X86)), "reject")

    def test_a_program_that_stops_running_rejects(self):
        broken = cell(speed=None, memory=None, status="wrong output")
        quicker = cell(speed=10, image="quick")
        scored = score(suite([quicker, broken]))
        self.assertEqual(len(scored["broken"]), 2)
        self.assertEqual(decide(scored)[0], "reject")

    def test_a_program_that_starts_running_is_a_gain(self):
        absent = cell(
            speed=None, memory=None, size=70000, small=70000, status="too large"
        )
        fits = cell(size=60000, small=60000, image="fits")
        cells = suite([fits], [absent], MOS)
        self.assertEqual(ratio(MOS, "speed", absent, fits), 0.5)
        self.assertEqual(ratio(MOS, "size", absent, fits), 60000 / 70000)
        self.assertEqual(verdict(cells), "accept")

    def test_a_program_too_large_on_both_sides_counts_by_its_size(self):
        before = cell(
            speed=None, memory=None, size=70000, small=70000, status="too large"
        )
        after = cell(
            speed=None, memory=None, size=69000, small=69000, status="too large"
        )
        self.assertEqual(verdict(suite([after], [before], MOS)), "accept")

    def test_an_unchanged_image_earns_nothing_from_a_noisy_count(self):
        self.assertEqual(ratio(X86, "memory", cell(), cell(memory=50)), 1.0)
        self.assertEqual(ratio(X86, "speed", cell(), cell(speed=900)), 1.0)

    def test_x86_instructions_within_their_jitter_are_the_same(self):
        old = cell(speed=100_000_000)
        new = cell(speed=100_000_900, image="two")
        self.assertEqual(ratio(X86, "speed", old, new), 1.0)
        self.assertEqual(ratio(WASM, "speed", old, new), 1.000009)
        beyond = cell(speed=100_001_100, memory=104, image="two")
        self.assertGreater(ratio(X86, "speed", old, beyond), 1.0)
        self.assertEqual(ratio(X86, "memory", old, beyond), 1.04)

    def test_each_targets_metric_weighs_the_same_however_many_programs(self):
        one = score(suite([cell(speed=500, image="b")]))
        four = score(suite([cell(speed=500, image="b") for _ in range(4)]))
        self.assertAlmostEqual(one["score"], four["score"])
        self.assertAlmostEqual(one["score"], 0.5**0.25)

    def test_a_changed_protected_path_rejects(self):
        quicker = suite([cell(speed=500, image="quick")])
        self.assertEqual(verdict(quicker, protected=["eval/ratchet.py"]), "reject")
        same = decide(score(suite([cell()])), protected=["RATCHET.md"])
        self.assertEqual(same, ("reject", ["changes protected paths: RATCHET.md"]))

    def test_a_loss_alone_rejects(self):
        larger = suite([cell(size=5001, image="large")])
        self.assertEqual(verdict(larger), "reject")

    def test_a_longer_time_needs_a_changed_image_and_the_band_twice(self):
        def timed(quickest, median=None, image="new"):
            median = median or quickest
            return dict(
                time=quickest * 1e6, time_median=median * 1e6, size_sha256=image
            )

        old = timed(100, image="old")
        self.assertTrue(slower(old, timed(111)))
        self.assertFalse(slower(old, timed(109)))
        self.assertFalse(slower(old, timed(111, image="old")))
        self.assertFalse(slower(timed(1, image="old"), timed(1.2)))
        self.assertTrue(slower(timed(1, image="old"), timed(1.3)))
        # One lucky run of the incumbent's, or one burst in the candidate's.
        self.assertFalse(slower(timed(100, 150, image="old"), timed(150)))
        self.assertFalse(slower(old, timed(100, 150)))

    def test_the_incumbent_is_the_trunk_unless_named(self):
        self.assertFalse(hasattr(ratchet, "incumbent_of"))
        self.assertIsNone(parser().parse_args(["eval"]).incumbent)

    def test_a_log_row_names_no_commit(self):
        summary = dict(
            verdict="neutral",
            reasons=["net gain 0.00006 is below 0.001"],
            score=0.99994,
            worst=1.00019,
            report="/r/20261118T020022Z-eval-dafe2bad-vs-be5235d3.json",
            speed=1.0,
            memory=1.0,
            size=0.99988,
            small=0.99986,
            compile=1.0,
        )
        summary["not a promotion"] = ["uncommitted changes in the candidate"]
        row = log_row(summary, "an idea").split("\t")
        header = (ratchet.REPO / "ratchet/log.tsv").read_text().splitlines()[0]
        self.assertEqual(tuple(header.split("\t")), LOG)
        self.assertNotIn("commit", LOG)
        self.assertEqual(len(row), len(LOG))
        fields = dict(zip(LOG, row))
        self.assertEqual(fields["idea"], "an idea")
        self.assertEqual(fields["size"], "0.99988")
        self.assertEqual(
            fields["verdict"],
            "neutral: net gain 0.00006 is below 0.001; "
            "not a promotion: uncommitted changes in the candidate",
        )
        self.assertEqual(fields["report"], Path(summary["report"]).name)
        summary |= {"verdict": "accept", "reasons": []}
        accepted = dict(zip(LOG, log_row(summary, "x").split("\t")))
        self.assertEqual(
            accepted["verdict"],
            "accept: not a promotion: uncommitted changes in the candidate",
        )


class Compilers(unittest.TestCase):
    """Each revision's compiler is built from that revision's sources."""

    def test_an_older_revision_is_not_given_a_newer_ones_build(self):
        with tempfile.TemporaryDirectory() as directory:
            repo, cache = Path(directory, "repo"), Path(directory, "cache")
            (repo / "src").mkdir(parents=True)
            (repo / "Cargo.toml").write_text(
                '[package]\nname = "faun"\nversion = "0.1.0"\nedition = "2024"\n'
            )
            (repo / "src/main.rs").touch()
            subprocess.run(
                ["cargo", "generate-lockfile", "--offline", "--quiet"],
                cwd=repo,
                check=True,
            )

            def commit(says, when):
                main = 'fn main() { println!("' + says + '"); }\n'
                (repo / "src/main.rs").write_text(main)
                dated = os.environ | {
                    "GIT_AUTHOR_DATE": when,
                    "GIT_COMMITTER_DATE": when,
                }
                for command in (["init", "-q"], ["add", "."], ["commit", "-qm", says]):
                    subprocess.run(
                        ["git", "-c", "user.name=t", "-c", "user.email=t@t"]
                        + ["-c", "commit.gpgsign=false", *command],
                        cwd=repo,
                        env=dated,
                        check=True,
                    )
                said = ["git", "rev-parse", "HEAD"]
                return subprocess.check_output(said, cwd=repo, text=True).strip()

            # The older commit's files are older than the newer's build.
            older = commit("older", "2001-01-01T00:00:00Z")
            newer = commit("newer", "2002-01-01T00:00:00Z")
            with mock.patch.multiple(ratchet, REPO=repo, CACHE=cache):
                sides = [ratchet.Side(newer), ratchet.Side(older)]
                for side in sides:
                    side.build()
                said = [
                    subprocess.check_output([side.binary], text=True).strip()
                    for side in sides
                ]
                described = [side.describe() for side in sides]
            self.assertEqual(said, ["newer", "older"])
            self.assertFalse(same_compiler(*described))
            # A build's target directory goes once its compiler is kept.
            self.assertEqual(list((cache / "builds").iterdir()), [])

    def test_one_compiler_from_two_sources_is_not_a_promotion(self):
        def side(source, compiler):
            return {"source": source, "compiler_sha256": compiler}

        self.assertTrue(same_compiler(side("a", "x"), side("b", "x")))
        self.assertFalse(same_compiler(side("a", "x"), side("b", "y")))
        self.assertFalse(same_compiler(side("a", "x"), side("a", "x")))
        # An uncommitted checkout's source is not known.
        self.assertFalse(same_compiler(side("a", "x"), side(None, "x")))


if __name__ == "__main__":
    unittest.main()
