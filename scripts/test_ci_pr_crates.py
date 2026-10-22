#!/usr/bin/env python3
"""Test battery for the change-to-crates mapping (scripts/ci_pr_crates.py,
the selection of the pre-commit clippy in scripts/ci_local.sh).

The contracts, pinned on the row shape (`<path>` TAB `<old path>`):
  - a crate-only change maps to those crates and their transitive dependents;
  - ANY non-crate path - and a rename's removed side too - fails safe to
    the full selection;
  - an undecidable list (empty input, an empty path row) fails safe to the
    full selection, never to an empty selection: a narrowed run that checks
    nothing would masquerade as green.

Run: python3 scripts/test_ci_pr_crates.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

import ci_pr_crates  # noqa: E402  (the tool under test)

MAPPER = SCRIPTS_DIR / "ci_pr_crates.py"


def run_mapper(rows: list[str]) -> tuple[int, str, dict[str, str]]:
    output = Path(tempfile.mkdtemp()) / "github-output"
    env = dict(os.environ)
    env["GITHUB_OUTPUT"] = str(output)
    listing = Path(tempfile.mkdtemp()) / "changes.tsv"
    listing.write_text("\n".join(rows) + "\n", encoding="utf-8")
    result = subprocess.run([sys.executable, str(MAPPER), str(listing)],
                            capture_output=True, text=True, env=env, check=False)
    outputs = {}
    for line in output.read_text().splitlines():
        key, _, value = line.partition("=")
        outputs[key] = value
    return result.returncode, result.stdout, outputs


class TheMappingTestCase(unittest.TestCase):

    def test_a_crate_only_change_narrows_to_those_crates(self):
        rc, out, outputs = run_mapper([
            "crates/eukhe-daemon/src/main.rs",
            "crates/eukhe-daemon/src/roster.rs",
            "crates/eukhe-tui/src/view/runs.rs",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "eukhe-cli,eukhe-daemon,eukhe-gateway,eukhe-tui")
        self.assertIn("crates (4: eukhe-cli, eukhe-daemon, eukhe-gateway, eukhe-tui)", outputs["scope"])

    def test_any_non_crate_path_fails_safe_to_the_full_selection(self):
        rc, out, outputs = run_mapper([
            "crates/eukhe-core/src/lib.rs",
            ".github/workflows/eukhe-release.yml",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertEqual(outputs["scope"], "all")
        self.assertIn("non-crate path .github/workflows/eukhe-release.yml", out)

    def test_a_renames_removed_side_counts_too(self):
        # A rename from a non-crate path INTO a crate: the change removed the
        # old path, so the full selection runs.
        rc, out, outputs = run_mapper([
            "crates/eukhe-cli/src/new.rs\tdocs/old-location.md",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertIn("non-crate path docs/old-location.md", out)

    def test_a_rename_within_crates_narrows_to_both_crates(self):
        rc, out, outputs = run_mapper([
            "crates/eukhe-tui/src/editor/selection.rs\tcrates/eukhe-tui/src/selection.rs",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "eukhe-cli,eukhe-gateway,eukhe-tui")

    def test_types_only_runs_every_crate(self):
        rc, out, outputs = run_mapper(["crates/eukhe-types/src/lib.rs"])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], ",".join(sorted(ci_pr_crates.WORKSPACE_DEPS)))

    def test_tui_only_runs_cli_and_gateway_too(self):
        rc, out, outputs = run_mapper(["crates/eukhe-tui/src/lib.rs"])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "eukhe-cli,eukhe-gateway,eukhe-tui")

    def test_an_unknown_crate_fails_safe(self):
        rc, out, outputs = run_mapper(["crates/eukhe-future/src/lib.rs"])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertIn("unknown crate eukhe-future", out)

    def test_an_empty_filename_row_fails_safe(self):
        # A row whose path column is empty must never narrow the selection
        # to nothing: the full selection runs instead.
        rc, out, outputs = run_mapper([
            "\tcrates/eukhe-core/src/lib.rs",
            "crates/eukhe-daemon/src/lib.rs",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertEqual(outputs["scope"], "all")
        self.assertIn("empty filename", out)

    def test_an_empty_list_fails_safe_to_the_full_selection(self):
        rc, out, outputs = run_mapper([])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertEqual(outputs["scope"], "all")

    def test_a_whitespace_prefixed_path_is_a_non_crate_path(self):
        # The fields are read raw: a path with a leading space (or any
        # non-crate prefix) must never be stripped into a crate mapping.
        rc, out, outputs = run_mapper([
            " crates/eukhe-core/src/lib.rs",
            "crates/eukhe-tui/src/lib.rs",
        ])
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs["crates"], "")
        self.assertIn("non-crate path  crates/eukhe-core/src/lib.rs", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
