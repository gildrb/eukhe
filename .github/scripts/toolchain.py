"""The pins of .github/scripts/toolchain.env (NAME=value lines; the Makefile
includes the same file): BEND_VERSION, LEAN_VERSION, BEND_SKILL_REV.

Used by .github/scripts/pinned_bend.py, pinned_skill.py and ci_local.py.
"""

from __future__ import annotations

from pathlib import Path

ENV = Path(__file__).resolve().parent / "toolchain.env"


def pins() -> dict[str, str]:
    """Every NAME=value of toolchain.env (comments and blank lines skipped)."""
    values = {}
    for line in ENV.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            name, _, value = line.partition("=")
            values[name] = value
    return values
