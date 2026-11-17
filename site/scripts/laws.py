#!/usr/bin/env python3
"""The site's laws (LAWS.bend, laws/vim/), its own and apart from Eukhe's:
every proof PROOF.bend imports checks, by the checker and by Lean
(`--verdict`, Lean as ../.github/scripts/toolchain.env pins it), with the
repository's pinned Bend (../.github/scripts/pinned_bend.py); then LAWS.lock
holds the laws as they are (the bend skill's `gate.py --lock-only`;
BEND_SKILL: the skill directory, default the commit
../.github/scripts/toolchain.env pins, ../.github/scripts/pinned_skill.py).

Usage (in site/, `npm run laws`): python3 scripts/laws.py
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SITE.parent / ".github" / "scripts"))

import pinned_bend  # noqa: E402
import pinned_skill  # noqa: E402


def main() -> int:
    os.chdir(SITE)
    bend = pinned_bend.find()
    if bend is None:
        print(pinned_bend.missing(), file=sys.stderr)
        return 1
    for flags in ([], ["--verdict"]):
        result = subprocess.run([bend, "PROOF.bend", *flags], stdout=subprocess.PIPE, text=True)
        out = result.stdout.rstrip("\n")
        print(out, flush=True)
        if result.returncode:
            return result.returncode
        if "ALL PROOFS CHECK" not in out.split("\n"):
            return 1
    skill = os.environ.get("BEND_SKILL")
    if not skill:
        try:
            skill = str(pinned_skill.skill_dir())
        except pinned_skill.Unpinned as error:
            print(error, file=sys.stderr)
            return 1
    return subprocess.run(["python3", f"{skill}/scripts/gate.py", ".", "--lock-only"]).returncode


if __name__ == "__main__":
    raise SystemExit(main())
