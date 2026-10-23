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
import ./laws/m.bend as M
"""

LAWS_M = """import Base
import ../bend/m.bend as Mm

law m_one:
  {Mm.one == 1n : Nat}
"""

PROOF = """import Base
import ./LAWS.bend as Laws
import ./proof/m/m_one.bend as PMOne
"""

FILL = """import Base
import ../../laws/m.bend as M

def M.m_one():
  {==}
"""


class LayoutTestCase(unittest.TestCase):
    def tree(self, files: dict[str, str]) -> Path:
        root = Path(tempfile.mkdtemp())
        base = {
            "LAWS.bend": LAWS,
            "laws/m.bend": LAWS_M,
            "PROOF.bend": PROOF,
            "proof/m/m_one.bend": FILL,
            "bend/m.bend": "import Base\n",
        }
        for rel, text in {**base, **files}.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)
        return root

    def test_the_layout_passes(self) -> None:
        self.assertEqual(gaps_of(self.tree({})), [])

    def test_laws_in_laws_bend_pass(self) -> None:
        laws = "import Base\nimport ./bend/m.bend as Mm\n\nlaw m_one:\n  {Mm.one == 1n : Nat}\n"
        fill = "import Base\nimport ../../LAWS.bend as Laws\n\ndef Laws.m_one():\n  {==}\n"
        root = self.tree({"LAWS.bend": laws, "proof/m/m_one.bend": fill})
        (root / "laws" / "m.bend").unlink()
        self.assertEqual(gaps_of(root), [])

    def test_an_unproven_law_fails(self) -> None:
        root = self.tree({"PROOF.bend": "import Base\nimport ./LAWS.bend as Laws\n"})
        (root / "proof" / "m" / "m_one.bend").unlink()
        self.assertEqual(gaps_of(root), ["laws/m.bend: law m_one has no fill in a proof/ file PROOF.bend imports"])

    def test_a_fill_proof_bend_does_not_import_fails(self) -> None:
        gaps = gaps_of(self.tree({"PROOF.bend": "import Base\nimport ./LAWS.bend as Laws\n"}))
        self.assertEqual(gaps, [
            "proof/m/m_one.bend: proves law m_one; every proof lives in a proof/ file PROOF.bend imports",
            "laws/m.bend: law m_one has no fill in a proof/ file PROOF.bend imports",
        ])

    def test_a_def_in_proof_bend_fails(self) -> None:
        gaps = gaps_of(self.tree({"PROOF.bend": PROOF + "\ndef x() -> Nat:\n  0n\n"}))
        self.assertEqual(gaps, ["PROOF.bend: holds a def; it only imports the proof/ files"])

    def test_a_laws_file_not_imported_fails(self) -> None:
        gaps = gaps_of(self.tree({"laws/x.bend": "import Base\n"}))
        self.assertEqual(gaps, ["laws/x.bend: LAWS.bend does not import it"])

    def test_a_law_outside_the_laws_fails(self) -> None:
        gaps = gaps_of(self.tree({"bend/m.bend": "import Base\n\nlaw stray:\n  {1n == 1n : Nat}\n"}))
        self.assertEqual(gaps, ["bend/m.bend: declares law stray; every law lives in LAWS.bend or laws/"])

    def test_a_proof_outside_proof_fails(self) -> None:
        lemma = "import Base\nimport ../laws/m.bend as L\n\ndef L.m_one():\n  {==}\n"
        gaps = gaps_of(self.tree({"bend/m_more.bend": lemma}))
        self.assertEqual(gaps, ["bend/m_more.bend: proves law m_one; every proof lives in a proof/ file PROOF.bend imports"])

    def test_a_proof_file_outside_proof_fails(self) -> None:
        gaps = gaps_of(self.tree({"bend/proof_m.bend": "import Base\n"}))
        self.assertEqual(gaps, ["bend/proof_m.bend: every proof and proof lemma lives in a proof/ file"])

    def test_a_law_file_without_its_fill_fails(self) -> None:
        proof = PROOF + "import ./proof/m/m_two.bend as PMTwo\n"
        gaps = gaps_of(self.tree({"PROOF.bend": proof, "proof/m/m_two.bend": "import Base\n"}))
        self.assertEqual(gaps, ["proof/m/m_two.bend: does not fill law m_two"])

    def test_a_proof_in_another_area_fails(self) -> None:
        proof = "import Base\nimport ./LAWS.bend as Laws\nimport ./proof/x/m_one.bend as PMOne\n"
        root = self.tree({"PROOF.bend": proof, "proof/x/m_one.bend": FILL})
        (root / "proof" / "m" / "m_one.bend").unlink()
        self.assertEqual(gaps_of(root), ["proof/x/m_one.bend: law m_one lives in laws/m.bend; its proof in proof/m/"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
