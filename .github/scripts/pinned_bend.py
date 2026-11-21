#!/usr/bin/env python3
"""Print the path of the Bend executable at the BEND_VERSION that
.github/scripts/toolchain.env pins (the single pin): mise's install of that
exact version when mise has one, else the first `bend` on PATH whose `bend
version` is it. A version manager's global default (or its shims) may be
another release; the gates run this one. Exits 1, naming the missing
version, when none is installed.

Usage: python3 .github/scripts/pinned_bend.py
(.github/scripts/ci_local.py imports `find`.)
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

from toolchain import pins

ROOT = Path(__file__).resolve().parents[2]


def is_pinned(path: str, version: str) -> bool:
    if not (os.path.isfile(path) and os.access(path, os.X_OK)):
        return False
    try:
        out = subprocess.run([path, "version"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True).stdout
    except OSError:
        return False
    return out.rstrip("\n") == f"bend {version}"


def find() -> str | None:
    """The pinned Bend's path, or None when it is not installed."""
    version = pins()["BEND_VERSION"]
    if shutil.which("mise") is not None:
        where = subprocess.run(
            ["mise", "where", f"github:bendlang/bend@{version}"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        ).stdout.rstrip("\n")
        if where and is_pinned(f"{where}/bin/bend", version):
            return f"{where}/bin/bend"
    for directory in os.environ.get("PATH", "").split(os.pathsep):
        candidate = os.path.join(directory or ".", "bend")
        if is_pinned(candidate, version):
            return candidate
    return None


def missing() -> str:
    version = pins()["BEND_VERSION"]
    return (
        f"Bend {version} (.github/scripts/toolchain.env) is not installed: install it "
        f"(mise install github:bendlang/bend@{version}, or https://bend-lang.com/install.sh) "
        "and keep it on PATH or in mise."
    )


def main() -> int:
    bend = find()
    if bend is None:
        print(missing(), file=sys.stderr)
        return 1
    print(bend)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
