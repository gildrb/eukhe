#!/usr/bin/env python3
"""Tests of bend_proofs.py: a change selects the proofs that read it, and
every proof of a law module those proofs load.

Run: python3 scripts/test_bend_proofs.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bend_proofs import select  # noqa: E402  (the tool under test)


def law_module(model: str, *laws: str) -> str:
    return f"import Base\nimport ../bend/{model}.bend as M\n" + "".join(
        f"\nlaw {law}:\n  {{M.one == 1n : Nat}}\n" for law in laws
    )


def fill(area: str, law: str, *also: str) -> str:
    extra = "".join(f"import ../../laws/{a}.bend as {a.upper()}\n" for a in also)
    return f"import Base\nimport ../../laws/{area}.bend as {area.upper()}\n{extra}\ndef {area.upper()}.{law}():\n  {{==}}\n"


ENTRIES = [
    ("a", "a_one", ("c",)),  # a_one also reads the law module c
    ("b", "b_one", ()),
    ("b", "b_two", ()),
    ("c", "c_one", ()),
    ("d", "d_one", ()),
    ("d", "d_two", ()),
    ("d", "d_three", ()),
]
PROOF = "import Base\nimport ./LAWS.bend as Laws\n" + "".join(
    f"import ./proof/{area}/{law}.bend as P{k}\n" for k, (area, law, _) in enumerate(ENTRIES)
)
FILES = {
    "LAWS.bend": "import Base\n" + "".join(f"import ./laws/{a}.bend as {a.upper()}\n" for a in "abcd"),
    "PROOF.bend": PROOF,
    "laws/a.bend": law_module("a", "a_one"),
    "laws/b.bend": law_module("b", "b_one", "b_two"),
    "laws/c.bend": law_module("c", "c_one"),
    "laws/d.bend": law_module("d", "d_one", "d_two", "d_three"),
    **{f"bend/{m}.bend": "import Base\n" for m in ("a", "b", "c", "d", "core")},
    **{f"proof/{area}/{law}.bend": fill(area, law, *also) for area, law, also in ENTRIES},
    "scripts/toolchain.env": "BEND_VERSION=2\n",
}


def entries(*laws: str) -> list[str]:
    return [f"./proof/{area}/{law}.bend" for area, law, _ in ENTRIES if law in laws]


class SelectTestCase(unittest.TestCase):
    def repo(self) -> Path:
        root = Path(tempfile.mkdtemp())
        for rel, text in FILES.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)
        for args in (["init", "-q"], ["add", "-A"], ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "base"]):
            subprocess.run(["git", "-C", str(root), *args], check=True)
        return root

    def test_no_change_selects_nothing(self) -> None:
        self.assertEqual(select(self.repo(), "HEAD"), ("none: no proof reads a changed file", []))

    def test_a_model_change_selects_its_proofs_and_the_laws_they_load(self) -> None:
        root = self.repo()
        (root / "bend/a.bend").write_text("import Base\n# changed\n")
        self.assertEqual(select(root, "HEAD"), ("2 of 7 proof files", entries("a_one", "c_one")))

    def test_a_model_read_by_two_areas_selects_both(self) -> None:
        root = self.repo()
        (root / "bend/c.bend").write_text("import Base\n# changed\n")
        self.assertEqual(select(root, "HEAD"), ("2 of 7 proof files", entries("a_one", "c_one")))

    def test_a_new_law_selects_its_area_and_the_new_proof(self) -> None:
        root = self.repo()
        (root / "laws/b.bend").write_text(law_module("b", "b_one", "b_two", "b_three"))
        (root / "proof/b/b_three.bend").write_text(fill("b", "b_three"))
        (root / "PROOF.bend").write_text(PROOF + "import ./proof/b/b_three.bend as PNew\n")
        self.assertEqual(
            select(root, "HEAD"),
            ("3 of 8 proof files", entries("b_one", "b_two") + ["./proof/b/b_three.bend"]),
        )

    def test_the_compiled_core_selects_no_proof(self) -> None:
        root = self.repo()
        (root / "bend/core.bend").write_text("import Base\n# regenerated\n")
        self.assertEqual(select(root, "HEAD"), ("none: no proof reads a changed file", []))

    def test_half_the_proofs_run_everything(self) -> None:
        root = self.repo()
        (root / "bend/b.bend").write_text("import Base\n# changed\n")
        (root / "bend/d.bend").write_text("import Base\n# changed\n")
        self.assertEqual(select(root, "HEAD"), ("full: 5 of 7 proof files", []))

    def test_the_bend_pin_runs_everything(self) -> None:
        root = self.repo()
        (root / "scripts/toolchain.env").write_text("BEND_VERSION=3\n")
        self.assertEqual(select(root, "HEAD"), ("full: scripts/toolchain.env changed", []))

    def test_a_non_import_line_of_the_index_runs_everything(self) -> None:
        root = self.repo()
        (root / "PROOF.bend").write_text(PROOF + "def x() -> Nat:\n  0n\n")
        self.assertEqual(
            select(root, "HEAD"), ("full: a line of PROOF.bend other than an import changed", [])
        )


if __name__ == "__main__":
    unittest.main()
