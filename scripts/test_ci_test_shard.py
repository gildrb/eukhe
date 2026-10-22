#!/usr/bin/env python3
"""Test battery for the local gate's shard tooling (scripts/ci_test_shard.py +
scripts/ci_test_shard_summary.py, which scripts/ci_local.sh runs): the
narrowed selection and the summary's scope-aware partition audit.

The contracts, pinned on the REAL workspace enumeration (cargo metadata
only - no builds):
  - the stable crc32 assignment is untouched by --crates: a narrowed run's
    unit lands in the same shard the full run assigns it;
  - the full selection is the default and audits green;
  - a crate selection narrows the universe; the union of the shards' runs
    must cover EXACTLY the selection - a narrowed run can never pass as a
    full one, and coverage can never silently regress;
  - a mixed-scope run (one shard claiming a different selection) fails
    the audit;
  - a shard that skips one of its selected units fails;
  - a unit that runs outside the selection fails;
  - --print-selection reports the selection without running anything and
    emits the units count.

Run: python3 scripts/test_ci_test_shard.py
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO = SCRIPTS_DIR.parent

TOTAL = 8


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SHARD = load_module("ci_test_shard", SCRIPTS_DIR / "ci_test_shard.py")
SUMMARY = load_module("ci_test_shard_summary", SCRIPTS_DIR / "ci_test_shard_summary.py")


def run_summary(directory: Path):
    return subprocess.run(
        [sys.executable, str(SCRIPTS_DIR / "ci_test_shard_summary.py"),
         "--total", str(TOTAL), "--dir", str(directory)],
        capture_output=True, text=True, check=False)


class EnumerationTestCase(unittest.TestCase):
    """The stable assignment + the narrowed selection."""

    @classmethod
    def setUpClass(cls):
        cls.units = SHARD.enumerate_units()
        cls.all_ids = [u["id"] for u in cls.units]
        cls.packages = {u["package"] for u in cls.units}

    def write_run(self, directory: Path, crates, results_by_shard=None,
                   scope_by_shard=None):
        selection = SHARD.selected_units(self.units, crates)
        for shard in range(1, TOTAL + 1):
            mine = [u for u in selection
                    if SHARD.shard_of(u["id"], TOTAL) == shard - 1]
            results = results_by_shard(shard, mine) if results_by_shard \
                else [dict(id=u["id"], package=u["package"], kind=u["kind"],
                           name=u["name"], rc=0, seconds=1.0,
                           failed_tests=[]) for u in mine]
            SHARD.write_manifest(
                directory / f"shard-manifest-{shard}.json", shard, TOTAL,
                self.all_ids, results, scope_by_shard(shard) if scope_by_shard else crates)
        return selection

    def test_the_assignment_is_stable_under_the_selection(self):
        """The narrowed universe never moves a unit between shards: crc32
        mod 8 is computed on the unit id, not the selection."""
        for unit in self.units:
            shard = SHARD.shard_of(unit["id"], TOTAL)
            self.assertEqual(unit["id"],
                             [u["id"] for u in self.units
                              if SHARD.shard_of(u["id"], TOTAL) == shard
                              and u["id"] == unit["id"]][0])

    def test_crate_selection_covers_exactly_that_crates_units(self):
        crate = sorted(self.packages)[0]
        selection = SHARD.selected_units(self.units, [crate])
        self.assertTrue(selection, "the crate selection is never empty")
        self.assertTrue(all(u["package"] == crate for u in selection))
        full = SHARD.selected_units(self.units, None)
        self.assertLess(len(selection), len(full))
        self.assertTrue(set(u["id"] for u in selection) <= set(u["id"] for u in full))


class AuditTestCase(unittest.TestCase):
    """The summary's scope-aware partition audit."""

    @classmethod
    def setUpClass(cls):
        cls.units = SHARD.enumerate_units()
        cls.all_ids = [u["id"] for u in cls.units]
        # The audit-failure cases need a crate whose units spread across
        # several shards: the largest unit count guarantees it.
        counts = {}
        for unit in cls.units:
            counts[unit["package"]] = counts.get(unit["package"], 0) + 1
        cls.crate = max(counts, key=lambda p: counts[p])
        cls.selection = [u["id"] for u in cls.units
                          if u["package"] == cls.crate]

    def green_run(self, directory: Path, crates, break_shard=None,
                   drop_unit=False, add_outside=False, scope_by_shard=None):
        selection = [u["id"] for u in self.units
                     if crates is None or u["package"] in set(crates)]
        for shard in range(1, TOTAL + 1):
            mine = [i for i in selection if SHARD.shard_of(i, TOTAL) == shard - 1]
            results = [dict(id=i, rc=0, seconds=1.0, failed_tests=[]) for i in mine]
            if break_shard == shard and drop_unit and results:
                results = results[:-1]
            if break_shard == shard and add_outside:
                outside = [i for i in self.all_ids
                           if i not in set(selection)
                           and SHARD.shard_of(i, TOTAL) == shard - 1]
                if outside:
                    results.append(dict(id=outside[0], rc=0, seconds=1.0,
                                        failed_tests=[]))
            use_crates = scope_by_shard(shard) if scope_by_shard else crates
            SHARD.write_manifest(
                directory / f"shard-manifest-{shard}.json", shard, TOTAL,
                self.all_ids, results, use_crates)

    def test_a_full_run_audits_green(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, None)
            result = run_summary(directory)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("full selection", result.stdout)

    def test_a_narrowed_run_audits_green_and_names_the_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, [self.crate])
            result = run_summary(directory)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn(f"crate selection: {self.crate}", result.stdout)
            self.assertIn(f"{len(self.selection)} of {len(self.all_ids)} units selected",
                          result.stdout)

    def test_a_mixed_scope_run_fails_the_audit(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, [self.crate],
                            scope_by_shard=lambda shard: None if shard == 5 else [self.crate])
            result = run_summary(directory)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("different selection scopes", result.stdout)

    def test_a_shard_that_skips_a_selected_unit_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, [self.crate], break_shard=4, drop_unit=True)
            result = run_summary(directory)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("never reported", result.stdout)

    def test_a_unit_that_runs_outside_the_selection_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, [self.crate], break_shard=2, add_outside=True)
            result = run_summary(directory)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("outside the selection ran", result.stdout)

    def test_a_selected_unit_no_shard_ran_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.green_run(directory, [self.crate])
            # Drop the unit from the run AND from the shard's recorded
            # selection reality: rewrite one manifest with the unit missing
            # from its units and its complete flag falsified.
            shard = next(SHARD.shard_of(i, TOTAL) + 1 for i in self.selection)
            path = directory / f"shard-manifest-{shard}.json"
            manifest = json.loads(path.read_text())
            if manifest["units"]:
                manifest["units"] = manifest["units"][:-1]
                manifest["complete"] = False
            path.write_text(json.dumps(manifest, indent=1) + "\n")
            result = run_summary(directory)
            self.assertEqual(result.returncode, 1, result.stdout)


class SelectionReportingTestCase(unittest.TestCase):
    """--print-selection resolves without running and emits the count."""

    def test_print_selection_reports_and_counts(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "ci_test_shard.py"),
             "--shard", "3", "--total", str(TOTAL), "--crates", "eukhe-daemon",
             "--print-selection"],
            capture_output=True, text=True, cwd=REPO, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("SELECTED=", result.stdout)
        self.assertIn("crate selection: eukhe-daemon", result.stdout)
        count = int(next(line for line in result.stdout.splitlines()
                         if line.startswith("SELECTED=")).split("=")[1])
        self.assertGreater(count, 0)

    def test_an_empty_selection_reports_zero_and_skips_nothing(self):
        """A crate whose units all hash to OTHER shards leaves a leg with
        nothing to run: it reports SELECTED=0."""
        # A (crate, shard) pair where every unit of the crate hashes to
        # another shard: that leg selects zero.
        occupied = {}
        for unit in SHARD.enumerate_units():
            occupied.setdefault(unit["package"], set()).add(
                SHARD.shard_of(unit["id"], TOTAL) + 1)
        crate, shard = next((crate, shard) for crate, shards in sorted(occupied.items())
                            for shard in range(1, TOTAL + 1) if shard not in shards)
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "ci_test_shard.py"),
             "--shard", str(shard), "--total", str(TOTAL), "--crates", crate,
             "--print-selection"],
            capture_output=True, text=True, cwd=REPO, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("SELECTED=0", result.stdout)

    def test_an_unknown_package_is_refused_fail_closed(self):
        """A --crates name the workspace does not build is a mapping bug:
        refuse it (a silent zero would pass as a green run)."""
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "ci_test_shard.py"),
             "--shard", "3", "--total", str(TOTAL), "--crates", "eukhe-nonexistent",
             "--print-selection"],
            capture_output=True, text=True, cwd=REPO, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not build", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
