#!/usr/bin/env python3
"""Tests of check_laws_wired.py: each layout rule fails on a tree that breaks it.

Run: python3 scripts/test_check_laws_wired.py
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_laws_wired import gaps_of  # noqa: E402  (the tool under test)

LAWS = """import Base
import ./bend/m.bend as M

law m_one:
  {M.one == 1n : Nat}
"""

PROOF = """import Base
import ./LAWS.bend as Laws

def Laws.m_one():
  {==}
"""


class LayoutTestCase(unittest.TestCase):
    def tree(self, files: dict[str, str]) -> Path:
        root = Path(tempfile.mkdtemp())
        base = {"LAWS.bend": LAWS, "PROOF.bend": PROOF, "bend/m.bend": "import Base\n"}
        for rel, text in {**base, **files}.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)
        return root

    def test_the_layout_passes(self) -> None:
        self.assertEqual(gaps_of(self.tree({})), [])

    def test_an_unproven_law_fails(self) -> None:
        gaps = gaps_of(self.tree({"PROOF.bend": "import Base\nimport ./LAWS.bend as Laws\n"}))
        self.assertEqual(gaps, ["LAWS.bend: law m_one has no fill def Laws.m_one( in PROOF.bend"])

    def test_a_laws_directory_fails(self) -> None:
        gaps = gaps_of(self.tree({"laws/x.bend": "import Base\n"}))
        self.assertIn("laws/: every law lives in LAWS.bend; remove the directory", gaps)

    def test_a_law_outside_laws_bend_fails(self) -> None:
        gaps = gaps_of(self.tree({"bend/m.bend": "import Base\n\nlaw stray:\n  {1n == 1n : Nat}\n"}))
        self.assertEqual(gaps, ["bend/m.bend: declares law stray; every law lives in LAWS.bend"])

    def test_a_proof_outside_proof_bend_fails(self) -> None:
        lemma = "import Base\nimport ../LAWS.bend as L\n\ndef L.m_one():\n  {==}\n"
        gaps = gaps_of(self.tree({"bend/m_more.bend": lemma}))
        self.assertEqual(gaps, ["bend/m_more.bend: proves law m_one; every proof lives in PROOF.bend"])

    def test_a_proof_file_outside_proof_bend_fails(self) -> None:
        gaps = gaps_of(self.tree({"bend/proof_m.bend": "import Base\n"}))
        self.assertEqual(gaps, ["bend/proof_m.bend: every proof and proof lemma lives in PROOF.bend"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
