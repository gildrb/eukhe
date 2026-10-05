#!/usr/bin/env python3
"""Tests for the rolling-version stamp (stamp_version.py).

Run: python3 scripts/release/test_stamp_version.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import stamp_version  # noqa: E402  (same release-scripts directory)

LOCK = """\
version = 4

[[package]]
name = "anyhow"
version = "1.0.98"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "e16d2d3311acee920a9eb8d33b8cbc1787ce4a264e85f964c2404b969bdcd487"

[[package]]
name = "eukhe-cli"
version = "0.9.9-eukhe.1"
dependencies = [
 "anyhow",
 "eukhe-core",
]

[[package]]
name = "eukhe-core"
version = "0.9.9-eukhe.1"
dependencies = [
 "anyhow",
]

[[package]]
name = "eukhe-lookalike"
version = "0.9.9-eukhe.1"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "0000000000000000000000000000000000000000000000000000000000000000"
"""


class StampLock(unittest.TestCase):

    def test_only_workspace_eukhe_versions_move(self):
        self.assertEqual(
            stamp_version.stamp_lock(LOCK, "0.9.9-eukhe.1", "0.9.9-main.42"),
            LOCK.replace(
                'name = "eukhe-cli"\nversion = "0.9.9-eukhe.1"',
                'name = "eukhe-cli"\nversion = "0.9.9-main.42"',
            ).replace(
                'name = "eukhe-core"\nversion = "0.9.9-eukhe.1"',
                'name = "eukhe-core"\nversion = "0.9.9-main.42"',
            ),
        )

    def test_a_drifted_workspace_entry_fails(self):
        with self.assertRaises(SystemExit) as raised:
            stamp_version.stamp_lock(LOCK, "0.9.8", "0.9.9-main.42")
        self.assertIn("expected the workspace version '0.9.8'", str(raised.exception))

    def test_a_lock_without_workspace_entries_fails(self):
        with self.assertRaises(SystemExit) as raised:
            stamp_version.stamp_lock('version = 4\n', "0.9.9-eukhe.1", "0.9.9-main.42")
        self.assertIn("no eukhe-* workspace package entries", str(raised.exception))


class StampManifest(unittest.TestCase):

    def test_only_the_workspace_package_version_moves(self):
        manifest = (
            '[package]\nversion = "1.0.0"\n\n'
            '[workspace.package]\nversion = "0.9.9-eukhe.1"\nedition = "2021"\n\n'
            '[dependencies]\nversion = "2"\n'
        )
        self.assertEqual(
            stamp_version.stamp(manifest, "0.9.9-main.42"),
            manifest.replace('version = "0.9.9-eukhe.1"', 'version = "0.9.9-main.42"'),
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
