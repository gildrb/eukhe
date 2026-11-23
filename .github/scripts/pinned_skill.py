#!/usr/bin/env python3
"""Print the path of the bend skill (its bend/ folder) at the commit
BEND_SKILL_REV that .github/scripts/toolchain.env pins: a clone of
github.com/gildrb/skills in ~/.cache/eukhe/bend-skill/<rev>, made once. The
lock gate runs this gate.py (.github/scripts/ci_local.py laws_lock and
relock; gildrb/eukhe-site's scripts/laws.py, from its checkout of eukhe):
its verdict on LAWS.lock depends on the gate's code, so the gate is pinned
like Bend. Exits 1, naming the commit, when the clone fails, or the cache
holds another commit or changed files.

Usage: python3 .github/scripts/pinned_skill.py
(.github/scripts/ci_local.py and gildrb/eukhe-site's scripts/laws.py import
`skill_dir`.)
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from toolchain import pins

REPOSITORY = "https://github.com/gildrb/skills"


class Unpinned(Exception):
    """The pinned skill cannot be had; the message says why."""


def skill_dir() -> Path:
    """The bend/ folder of the skill at BEND_SKILL_REV, cloned when missing."""
    rev = pins()["BEND_SKILL_REV"]
    pin = f"{rev} (.github/scripts/toolchain.env BEND_SKILL_REV)"
    clone = Path.home() / ".cache" / "eukhe" / "bend-skill" / rev
    if not clone.is_dir():
        clone.parent.mkdir(parents=True, exist_ok=True)
        tmp = tempfile.mkdtemp(prefix=f"{rev}.", dir=clone.parent)
        try:
            # git's own output goes to stderr: stdout is the path.
            if subprocess.run(["git", "clone", "--quiet", "--no-checkout", REPOSITORY, tmp], stdout=sys.stderr).returncode:
                raise Unpinned(f"the bend skill at {pin} could not be cloned from {REPOSITORY}")
            checkout = ["git", "-C", tmp, "-c", "advice.detachedHead=false", "checkout", "--quiet", rev]
            if subprocess.run(checkout, stdout=sys.stderr).returncode:
                raise Unpinned(f"the bend skill at {pin} could not be checked out from {REPOSITORY}")
            if not clone.is_dir():
                os.rename(tmp, clone)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    have = subprocess.run(
        ["git", "-C", str(clone), "rev-parse", "HEAD"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True
    ).stdout.strip()
    if have != rev or subprocess.run(
        ["git", "-C", str(clone), "status", "--porcelain", "--untracked-files=no"], stdout=subprocess.PIPE, text=True
    ).stdout.strip():
        raise Unpinned(f"{clone} is not the bend skill at {pin}: it holds {have or 'no commit'} or changed files. Remove it and run again.")
    return clone / "bend"


def main() -> int:
    try:
        print(skill_dir())
    except Unpinned as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
