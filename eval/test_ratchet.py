"""Decision boundaries of the ratchet. Run with python3 -B test_ratchet.py."""

import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import ratchet
from ratchet import (
    LOG,
    MOS,
    PROBE,
    SERIES,
    WASM,
    X86,
    again_size,
    decide,
    families,
    family_rows,
    idea_of,
    log_row,
    noted,
    parser,
    probe_changes,
    probes,
    ratio,
    score,
    same_compiler,
    same_work,
    slower,
    standings,
    table,
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
    """Cells of one target, a workload for each candidate."""
    incumbents = incumbents or [cell() for _ in candidates]
    return {
        (target, f"program-{at}"): {"incumbent": old, "candidate": new}
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

    def test_a_memory_past_the_guard_where_the_heaps_arena_falls_is_noted(self):
        # x86-64 collatz under octagons: a fourth 512 KiB arena at 20,000,
        # and less than the incumbent at 15,000.
        quicker = cell(speed=100, image="quick")
        arena = cell(memory=488, image="arena")
        cells = suite([quicker, arena], [cell(), cell(memory=376)], X86)
        self.assertEqual(verdict(cells), "reject")
        key = X86, "program-1"
        cells[key]["again"] = {"size": 15000, "incumbent": 336, "candidate": 308}
        scored = score(cells)
        self.assertEqual(decide(scored), ("accept", []))
        self.assertEqual(
            noted(scored),
            ["x86_64-linux program-1 memory is 29.8% worse but -8.3% at size 15000"],
        )
        # The memory still counts in the score as measured.
        self.assertGreater(scored["loss"], 0)

    def test_a_memory_past_the_guard_at_both_sizes_rejects(self):
        quicker = cell(speed=100, image="quick")
        more = cell(memory=488, image="more")
        cells = suite([quicker, more], [cell(), cell(memory=376)], X86)
        key = X86, "program-1"
        cells[key]["again"] = {"size": 15000, "incumbent": 290, "candidate": 336}
        self.assertEqual(verdict(cells), "reject")
        self.assertEqual(noted(score(cells)), [])
        # Within its slack there, it is not past the guard there.
        cells[key]["again"] |= {"incumbent": 40, "candidate": 50}
        self.assertEqual(verdict(cells), "accept")
        # Not running at the second size, it is past it.
        cells[key]["again"] |= {"candidate": None}
        self.assertEqual(verdict(cells), "reject")
        # And a 6502 memory past the guard at every size, as the sort's first
        # arena is, rejects.
        sort = suite(
            [quicker, cell(memory=1502, image="arena")],
            [cell(), cell(memory=804)],
            MOS,
        )
        sort[MOS, "program-1"]["again"] = {
            "size": 18,
            "incumbent": 750,
            "candidate": 1450,
        }
        self.assertEqual(verdict(sort), "reject")

    def test_only_a_memory_is_measured_again(self):
        quicker = cell(speed=100, image="quick")
        slow = cell(speed=1200, image="slow")
        cells = suite([quicker, slow], target=X86)
        cells[X86, "program-1"]["again"] = {
            "size": 1,
            "incumbent": 100,
            "candidate": 100,
        }
        self.assertEqual(verdict(cells), "reject")

    def test_memory_is_measured_again_at_three_quarters_of_its_size(self):
        workload = ratchet.Workload("p", Path(), "argument", {X86: 20000, MOS: 1})
        self.assertEqual(again_size(workload, X86), 15000)
        self.assertEqual(again_size(workload, MOS), 1)
        stepped = workload._replace(sizes={X86: 500}, step=10)
        self.assertEqual(again_size(stepped, X86), 370)

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

    def test_a_longer_time_doing_the_same_work_is_noted_not_rejected(self):
        # x86-64 checksum under octagons: as many instructions, its loop's
        # head across a cache line.
        def ran(instructions, branches=50_000_000, memory=9512, image="new"):
            return dict(
                speed=instructions,
                branches=branches,
                memory=memory,
                size_sha256=image,
                time=4.8e6,
                time_median=4.9e6,
            )

        old = ran(94_065_692, image="old") | {"time": 3.9e6, "time_median": 4e6}
        self.assertTrue(slower(old, ran(94_064_748)))
        self.assertTrue(same_work(old, ran(94_064_748, 50_040_000)))
        self.assertFalse(same_work(old, ran(93_900_000)))
        self.assertFalse(same_work(old, ran(94_064_748, 49_900_000)))
        self.assertFalse(same_work(old, ran(94_064_748, memory=9516)))
        self.assertFalse(same_work(old, ran(94_064_748, branches=None)))
        steady = [
            {
                "target": X86,
                "workload": "checksum",
                "metric": "time",
                "ratio": 1.197,
            }
        ]
        scored = score(suite([cell()]))
        self.assertEqual(decide(scored, slowed=steady)[0], "reject")
        self.assertEqual(decide(scored)[0], "no change")
        self.assertEqual(
            noted(scored, steady),
            [
                "x86_64-linux checksum time runs 19.7% longer with as many"
                " instructions and branches and the same memory"
            ],
        )

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
        summary |= {"noted": ["one", "two"], "not a promotion": []}
        noting = dict(zip(LOG, log_row(summary, "x").split("\t")))
        self.assertEqual(noting["verdict"], "accept: noted: one; two")
        summary |= {"verdict": "reject", "reasons": ["worse"]}
        noting = dict(zip(LOG, log_row(summary, "x").split("\t")))
        self.assertEqual(noting["verdict"], "reject: worse; noted: one; two")

    def test_a_row_records_the_measured_commits_subject(self):
        args = parser().parse_args(["eval", "--log"])
        self.assertTrue(args.log)
        self.assertIsNone(args.idea)
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            (repo / "main.fn").write_text("one\n")
            commit_all(repo, "Loops count down to zero\n\nThe body says why.")
            with mock.patch.object(ratchet, "REPO", repo):
                side = ratchet.Side(str(repo))
                self.assertEqual(idea_of(side, args.idea), "Loops count down to zero")
                (repo / "main.fn").write_text("two\n")
                side = ratchet.Side(str(repo))
                self.assertEqual(
                    idea_of(side),
                    "Loops count down to zero (with uncommitted changes)",
                )
                timed = parser().parse_args(
                    ["eval", "--log", "--idea", "the same, timed"]
                )
                self.assertEqual(idea_of(side, timed.idea), "the same, timed")

    def test_a_row_keeps_an_idea_on_one_line(self):
        summary = dict(
            verdict="accept",
            reasons=[],
            score=0.9,
            worst=1.0,
            report="/r/x.json",
            speed=1.0,
            memory=1.0,
            size=0.9,
            small=0.9,
            compile=1.0,
        )
        fields = dict(zip(LOG, log_row(summary, "one\ttwo\nthree").split("\t")))
        self.assertEqual(fields["idea"], "one two three")

    def test_pinning_passes_a_long_idea_on_and_resolves_only_checkouts(self):
        idea = "a change described at length " * 20
        self.assertGreater(len(idea.encode()), 255)
        argv = ["ratchet.py", "eval", ".", "--log", "--idea", idea, "--jobs", "2"]
        with (
            tempfile.TemporaryDirectory() as cache,
            mock.patch.object(sys, "argv", argv),
            mock.patch.dict(os.environ, clear=False) as env,
            mock.patch.object(ratchet, "CACHE", Path(cache)),
            # CI's checkout has no origin/main; HEAD holds an evaluator too.
            mock.patch.object(ratchet, "TRUNK", "HEAD"),
            mock.patch.object(ratchet, "export"),
            mock.patch.object(os, "execve") as execve,
        ):
            env.pop("RATCHET_PINNED", None)
            ratchet.pin(parser().parse_args(argv[1:]))
        passed = execve.call_args.args[1][2:]
        self.assertEqual(
            passed,
            ["eval", str(Path(".").resolve()), "--log", "--idea", idea, "--jobs", "2"],
        )
        # An idea that names a directory is still an idea.
        argv = ["ratchet.py", "eval", "--idea", ".", "."]
        self.assertEqual(ratchet.positionals(parser(), argv[1:]), [0, 3])


def probing(candidates, incumbents=None, target=X86):
    """Cells of probes on one target, a probe for each candidate."""
    incumbents = incumbents or [cell() for _ in candidates]
    return {
        (target, f"{PROBE}{at}"): {"incumbent": old, "candidate": new}
        for at, (old, new) in enumerate(zip(incumbents, candidates, strict=True))
    }


def commit_all(repo, message):
    for command in (["add", "-A"], ["commit", "-qm", message]):
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@t"]
            + ["-c", "commit.gpgsign=false", *command],
            cwd=repo,
            check=True,
        )
    said = ["git", "rev-parse", "HEAD"]
    return subprocess.check_output(said, cwd=repo, text=True).strip()


class Probes(unittest.TestCase):
    """Natural programs beside their workarounds, read from the trunk."""

    def test_a_probe_is_a_folder_with_its_twin_and_sizes(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            for name in ("power", "range"):
                (folder / name).mkdir()
                (folder / name / "main.fn").touch()
                (folder / name / "twin.fn").touch()
            (folder / "power/sizes").write_text(
                "# too large for the 6502\nx86_64-linux 1000\nwasm32-wasi 300\n"
            )
            (folder / "range/sizes").write_text("mos6502-sim65 8\n")
            # A folder without sizes is not a probe yet.
            (folder / "draft").mkdir()
            found = probes(folder)
        self.assertEqual([w.name for w in found], ["probe-power", "probe-range"])
        power, range_ = found
        self.assertTrue(power.probe)
        self.assertEqual(power.home, folder / "power")
        self.assertEqual(power.sizes, {X86: 1000, WASM: 300})
        self.assertEqual(range_.sizes, {MOS: 8})
        self.assertEqual(power.input, "argument")
        self.assertFalse(ratchet.WORKLOADS[0].probe)

    def test_the_trunks_probes_each_run_somewhere(self):
        for probe in probes():
            self.assertTrue(probe.sizes, probe.name)
            self.assertTrue((probe.home / "main.fn").exists(), probe.name)
            self.assertTrue((probe.home / "twin.fn").exists(), probe.name)

    def test_the_probes_count_as_one_more_target(self):
        quicker = cell(speed=500, image="quick")
        cells = suite([cell()]) | probing([quicker, cell(), cell(), cell()])
        scored = score(cells)
        self.assertIn("probes speed", scored["groups"])
        self.assertNotIn("x86_64-linux speed", scored["groups"])
        self.assertAlmostEqual(scored["groups"]["probes speed"], 0.5**0.25)
        # Eight groups: the suite's target's four, and the probes' four.
        self.assertAlmostEqual(scored["score"], 0.5 ** (1 / 4 / 8))

    def test_many_probes_weigh_no_more_than_one(self):
        quicker = cell(speed=500, image="quick")
        one = score(suite([cell()]) | probing([quicker]))
        many = score(suite([cell()]) | probing([quicker] * 10))
        self.assertAlmostEqual(one["score"], many["score"])

    def test_probes_compile_with_the_suite(self):
        cells = suite([cell(compile=1000)], [cell(compile=1000)])
        cells |= probing([cell(compile=500)], [cell(compile=1000)])
        self.assertAlmostEqual(score(cells)["groups"]["all compile"], 0.5**0.5)

    def test_a_probe_cell_more_than_a_tenth_worse_rejects(self):
        quicker = cell(speed=100, memory=10, image="quick")
        worse = cell(speed=1101, image="slow")
        cells = suite([quicker, quicker]) | probing([worse])
        self.assertEqual(verdict(cells), "reject")
        broken = cell(speed=None, memory=None, status="wrong output")
        self.assertEqual(verdict(suite([quicker]) | probing([broken])), "reject")

    def test_probes_differing_from_the_trunks_are_named(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            (repo / "probes/power").mkdir(parents=True)
            (repo / "probes/power/main.fn").write_text("old\n")
            (repo / "notes.md").write_text("old\n")
            trunk = commit_all(repo, "trunk")
            (repo / "notes.md").write_text("new\n")
            same = commit_all(repo, "notes")
            (repo / "probes/power/main.fn").write_text("new\n")
            changed = commit_all(repo, "probe")

            def side(commit, dirty=False):
                return SimpleNamespace(commit=commit, dirty=dirty, path=repo)

            with mock.patch.object(ratchet, "REPO", repo):
                self.assertEqual(probe_changes(side(same), trunk), [])
                self.assertEqual(
                    probe_changes(side(changed), trunk), ["probes/power/main.fn"]
                )
                subprocess.run(["git", "checkout", "-q", same], cwd=repo, check=True)
                (repo / "probes/key").mkdir()
                (repo / "probes/key/main.fn").write_text("new\n")
                subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
                self.assertEqual(
                    probe_changes(side(same, dirty=True), trunk),
                    ["probes/key/main.fn"],
                )


def family(spellings, name="count", target=X86):
    """Cells of one family's spellings on one target, each spelling's name to
    its incumbent and candidate."""
    return {
        (target, f"{PROBE}{name}-{spelling}"): {
            "incumbent": old,
            "candidate": new,
        }
        for spelling, (old, new) in spellings.items()
    }


def spelled(speeds, olds=(1000, 2000)):
    """A family of two spellings, `fast` and `slow`, at these speeds."""
    cells = {}
    for name, old, new in zip(("fast", "slow"), olds, speeds, strict=True):
        image = "same" if old == new else "new"
        cells[name] = (cell(speed=old, image="same"), cell(speed=new, image=image))
    return family(cells)


class Families(unittest.TestCase):
    """One computation spelled several ways, scored by its spread."""

    def test_a_family_is_probes_sharing_what_comes_before_a_hyphen(self):
        names = [
            "fasta",
            f"{PROBE}adler",
            f"{PROBE}count-u64",
            f"{PROBE}count-fold",
            # Alone with its prefix, a probe is a probe like another.
            f"{PROBE}bit-writer",
        ]
        self.assertEqual(
            families(names), {"count": [f"{PROBE}count-fold", f"{PROBE}count-u64"]}
        )

    def test_a_familys_spellings_share_their_sizes_and_twin(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            for name in ("count-fold", "count-u64"):
                (folder / name).mkdir()
                (folder / name / "main.fn").write_text(name)
                (folder / name / "twin.fn").write_text("twin")
                (folder / name / "sizes").write_text("x86_64-linux 1000\n")
            self.assertEqual(len(probes(folder)), 2)
            (folder / "count-u64/sizes").write_text("x86_64-linux 999\n")
            with self.assertRaises(SystemExit):
                probes(folder)
            (folder / "count-u64/sizes").write_text("x86_64-linux 1000\n")
            (folder / "count-u64/twin.fn").write_text("another")
            with self.assertRaises(SystemExit):
                probes(folder)

    def test_closing_a_spread_earns_half_again_what_its_spelling_does(self):
        cells = suite([cell()]) | spelled((1000, 1000))
        scored = score(cells)
        [speed] = [c for c in scored["spreads"] if c["metric"] == "speed"]
        self.assertEqual((speed["old"], speed["new"], speed["ratio"]), (2, 1, 0.5))
        self.assertAlmostEqual(scored["spread"]["speed"], 0.5)
        # Two spellings and a spread at half a spelling: the group is 2.5.
        self.assertAlmostEqual(scored["gain"], 1.5 / 2.5 * math.log(2) / 8)
        self.assertEqual(verdict(cells), "accept")
        # The same cell outside a family earns its own part alone.
        quicker = cell(speed=1000, image="quick")
        alone = probing([cell(), quicker], [cell(), cell(speed=2000)])
        alone |= suite([cell()])
        self.assertAlmostEqual(score(alone)["gain"], 1 / 2 * math.log(2) / 8)

    def test_opening_a_spread_costs_half_what_its_spelling_earns(self):
        scored = score(suite([cell()]) | spelled((500, 2000)))
        [speed] = [c for c in scored["spreads"] if c["metric"] == "speed"]
        self.assertEqual((speed["old"], speed["new"]), (2, 4))
        self.assertAlmostEqual(scored["loss"], scored["gain"] / 2)

    def test_slowing_the_best_spelling_to_close_a_spread_never_pays(self):
        cells = suite([cell()]) | spelled((1090, 2000))
        scored = score(cells)
        self.assertLess(scored["gain"], scored["loss"])
        self.assertEqual(verdict(cells), "reject")

    def test_a_spread_moved_within_a_counts_jitter_is_no_change(self):
        cells = suite([cell()]) | spelled((1000.001, 2000), (1000, 2000))
        scored = score(cells)
        self.assertTrue(all(c["ratio"] == 1.0 for c in scored["spreads"]))
        self.assertEqual(decide(scored)[0], "no change")

    def test_many_families_weigh_no_more_than_one(self):
        one = score(suite([cell()]) | spelled((1000, 1000)))
        many = suite([cell()])
        for at in range(10):
            many |= {
                (t, name.replace("count", f"count{at}")): sides
                for (t, name), sides in spelled((1000, 1000)).items()
            }
        self.assertEqual(len(score(many)["spreads"]), 40)
        self.assertAlmostEqual(one["score"], score(many)["score"])

    def test_a_family_with_a_spelling_not_running_has_no_spread(self):
        broken = cell(speed=None, memory=None, status="wrong output")
        cells = family({"fast": (cell(), cell()), "slow": (cell(), broken)})
        self.assertEqual(score(cells)["spreads"], [])
        self.assertEqual(verdict(suite([cell()]) | cells), "reject")

    def test_the_summary_and_the_standings_give_each_familys_spread(self):
        cells = spelled((1000, 1000))
        rows = "\n".join(family_rows(score(cells)["spreads"]))
        self.assertIn("count x86_64-linux", rows)
        self.assertIn("-50.00%    1.00", rows)
        report = {
            "candidate": {"commit": "abcdef0"},
            "started": "2026-11-19T00:00:00",
            "cells": [
                {"target": t, "workload": w, "c": {}} | sides
                for (t, w), sides in spelled((1000, 3000), (1000, 3000)).items()
            ],
        }
        written = standings(report)
        self.assertIn("## Families, x86_64-linux\n", written)
        self.assertIn("| count  | 3.00  | slow    | 1.00   | fast", written)


class Backend(unittest.TestCase):
    """One backend is measured, lab, and a cell is a program on a target."""

    def test_every_build_names_the_lab_backend(self):
        for small in (False, True):
            command = ratchet.faun_command(Path("faun"), WASM, small)
            at = command.index("--backend")
            self.assertEqual(command[at + 1], "lab")
            self.assertEqual("--small" in command, small)
        self.assertFalse(hasattr(ratchet, "BACKENDS"))

    def test_a_probes_twin_is_built_with_lab_too(self):
        built = []

        def build(side, target, small, workload, directory, file="main.fn"):
            built.append(ratchet.faun_command(side.binary, target, small) + [file])
            return None, "build: no", None, {}

        probe = ratchet.Workload(f"{PROBE}power", Path(), "argument", {X86: 1})
        side = SimpleNamespace(binary=Path("faun"))
        with mock.patch.object(ratchet, "faun_build", build):
            ratchet.c_build(X86, probe, Path(), side)
        [command] = built
        self.assertEqual(command[-1], "twin.fn")
        self.assertEqual(command[command.index("--backend") + 1], "lab")

    def test_the_summary_has_a_row_a_target(self):
        cells = suite([cell(size=4900, image="two")], target=X86)
        cells |= suite([cell()], target=MOS)
        for sides in cells.values():
            sides["c"] = {}
        lines = table(cells, score(cells)).splitlines()
        rows = [line.split()[0] for line in lines[2:5]]
        self.assertEqual(rows, [X86, WASM, MOS])
        self.assertNotIn("stock", "\n".join(lines))
        self.assertIn("x86_64-linux program-0 size", "\n".join(lines))

    def test_the_standings_give_a_table_a_target(self):
        cells = suite([cell()], target=X86)
        report = {
            "candidate": {"commit": "abcdef0"},
            "started": "2026-11-19T00:00:00",
            "cells": [
                {"target": t, "workload": w, "c": {"speed": 500}} | sides
                for (t, w), sides in cells.items()
            ],
        }
        written = standings(report)
        self.assertIn("\n## x86_64-linux\n", written)
        self.assertNotIn("stock", written)
        self.assertIn("| program-0", written)


def wrong(status="at 100: wrong output", **measures):
    """A cell whose image ran and printed other than the reference."""
    return cell(speed=None, memory=None, status=status, **measures)


class WrongCode(unittest.TestCase):
    """Wrong output fixed is accepted where nothing else is worse beyond
    what it pays for; and a probe's twin, built by each side, is held to
    the reference as its natural spelling is."""

    def many_probes(self, old, new, others=100, target=MOS):
        """One probe going from `old` to `new` among many unchanged, beside
        a suite on every target, so that its repair alone is below the
        neutral line, as one probe's is among the trunk's."""
        cells = probing([cell()] * others)
        for where in (X86, WASM, MOS):
            cells |= suite([cell()], target=where)
        cells[target, f"{PROBE}writer"] = {"incumbent": old, "candidate": new}
        return cells

    def test_wrong_output_fixed_with_nothing_else_moving_is_accepted(self):
        cells = self.many_probes(wrong(), cell())
        scored = score(cells)
        self.assertLess(scored["gain"] - scored["loss"], ratchet.MINIMUM)
        self.assertEqual(decide(scored), ("accept", []))
        [fixed] = scored["corrected"]
        self.assertEqual(fixed["workload"], f"{PROBE}writer")
        self.assertIn(f"corrects {MOS} {PROBE}writer", noted(scored)[0])

    def test_a_suite_programs_wrong_output_fixed_is_accepted(self):
        cells = suite([cell(), cell()], [wrong(), cell()], X86)
        self.assertEqual(verdict(cells), "accept")

    def test_a_program_that_only_starts_to_fit_corrects_nothing(self):
        absent = wrong(status="too large")
        scored = score(self.many_probes(absent, cell()))
        self.assertEqual(scored["corrected"], [])
        self.assertEqual(decide(scored)[0], "neutral")

    def test_a_fix_with_a_cell_past_the_guard_is_rejected(self):
        cells = self.many_probes(wrong(), cell())
        cells[X86, "program-0"]["candidate"] = cell(size=5600, image="large")
        self.assertEqual(verdict(cells), "reject")

    def test_a_fix_pays_for_no_more_than_half_its_repair(self):
        cells = self.many_probes(wrong(), cell())
        # The repair is two halvings among the probes; a suite cell a few
        # percent larger costs more than half of that.
        cells[X86, "program-0"]["candidate"] = cell(size=5100, image="large")
        scored = score(cells)
        self.assertGreater(2 * scored["loss"], scored["gain"])
        self.assertEqual(decide(scored)[0], "reject")
        cells[X86, "program-0"]["candidate"] = cell(size=5001, image="larger")
        self.assertEqual(verdict(cells), "accept")

    def test_a_fix_beside_a_break_is_rejected(self):
        cells = self.many_probes(wrong(), cell())
        cells[X86, "program-0"]["candidate"] = wrong()
        self.assertEqual(verdict(cells), "reject")

    def test_the_same_wrong_output_on_both_sides_is_no_change(self):
        cells = self.many_probes(wrong(), wrong())
        scored = score(cells)
        self.assertEqual(scored["corrected"], [])
        self.assertEqual(decide(scored)[0], "no change")

    def test_a_twin_that_runs_wrong_breaks_its_probes_cell(self):
        natural = cell() | {"image": "/i", "ns": 5, "branches": 9}
        held = ratchet.held_to_twin(natural, {"status": "at 8: wrong output"})
        self.assertEqual(held["status"], "twin at 8: wrong output")
        self.assertTrue(held["status"].endswith(ratchet.WRONG))
        for gone in ("speed", "memory", "ns", "branches", "image"):
            self.assertNotIn(gone, held)
        self.assertEqual((held["size"], held["small"]), (5000, 4000))
        crashed = ratchet.held_to_twin(natural, {"status": "at 8: exit 3: stack"})
        self.assertEqual(crashed["status"], "twin at 8: exit 3: stack")

    def test_a_twin_that_does_not_build_or_fit_says_nothing(self):
        for status in ("ok", "too large", "build: error: no"):
            self.assertEqual(ratchet.held_to_twin(cell(), {"status": status}), cell())
        # A natural spelling already not running keeps its own status.
        own = wrong()
        self.assertEqual(
            ratchet.held_to_twin(own, {"status": "at 8: wrong output"}), own
        )

    def test_a_twin_fixed_on_the_candidate_is_accepted(self):
        # The incumbent's compiler wrote the twin's wrong total on the 6502,
        # the natural spelling right on both sides: PR #64.
        twin_wrong = {"status": "at 8: wrong output"}
        old = ratchet.held_to_twin(cell(), twin_wrong)
        new = ratchet.held_to_twin(cell(), {"status": "ok"})
        self.assertEqual(verdict(self.many_probes(old, new)), "accept")

    def test_a_twin_broken_on_the_candidate_rejects(self):
        new = ratchet.held_to_twin(cell(), {"status": "small image at 3: wrong output"})
        scored = score(self.many_probes(cell(), new))
        self.assertEqual(len(scored["broken"]), 2)
        self.assertEqual(decide(scored)[0], "reject")

    def test_each_side_builds_and_holds_each_probes_twin(self):
        built = []

        def cell_of(side, label, target, workload, check, oracle, work, file="main.fn"):
            built.append((label, target, workload.name, file))
            if file == "twin.fn" and label == "incumbent":
                return {"status": "at 8: wrong output"}
            return cell()

        probe = ratchet.Workload(f"{PROBE}writer", Path(), "argument", {MOS: 8})
        kernel = ratchet.Workload("sieve", Path(), "argument", {MOS: 8})
        oracle = SimpleNamespace(case=lambda workload, size: None)
        sides = {"candidate": object(), "incumbent": object()}
        with (
            mock.patch.object(ratchet, "WORKLOADS", [kernel]),
            mock.patch.object(ratchet, "probes", lambda: [probe]),
            mock.patch.object(ratchet, "Oracle", lambda *_: oracle),
            mock.patch.object(ratchet, "faun_cell", cell_of),
            mock.patch.object(ratchet, "c_cell", lambda *_: {"status": "ok"}),
        ):
            cells, *_ = ratchet.measure(sides, 1, 2, "", Path())
        twins = sorted(b for b in built if b[3] == "twin.fn")
        self.assertEqual(
            twins,
            [
                ("candidate", MOS, f"{PROBE}writer", "twin.fn"),
                ("incumbent", MOS, f"{PROBE}writer", "twin.fn"),
            ],
        )
        writer = cells[MOS, f"{PROBE}writer"]
        self.assertEqual(set(writer), {"c", "incumbent", "candidate"})
        self.assertEqual(writer["incumbent"]["status"], "twin at 8: wrong output")
        self.assertEqual(writer["candidate"]["status"], "ok")
        self.assertEqual(writer["candidate"]["twin"], "ok")
        self.assertNotIn("twin", cells[MOS, "sieve"]["candidate"])
        self.assertEqual(verdict(cells), "accept")


class Series(unittest.TestCase):
    def test_a_log_row_is_in_the_evaluators_series_not_the_last_rows(self):
        summary = dict(
            verdict="accept",
            reasons=[],
            score=0.99,
            worst=1.0,
            report="/r/x.json",
            speed=1.0,
            memory=1.0,
            size=0.99,
            small=1.0,
            compile=1.0,
        )
        summary["not a promotion"] = []
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory, "ratchet/log.tsv")
            log.parent.mkdir()
            log.write_text("\t".join(LOG) + "\n" + "2\tolder\n")
            with mock.patch.object(ratchet, "REPO", Path(directory)):
                row = log_row(summary, "idea").split("\t")
        self.assertEqual(row[0], str(SERIES))

    def test_the_series_is_at_least_the_logs(self):
        rows = (ratchet.REPO / "ratchet/log.tsv").read_text().splitlines()[1:]
        logged = max(int(row.split("\t")[0]) for row in rows)
        self.assertGreaterEqual(SERIES, logged)


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
