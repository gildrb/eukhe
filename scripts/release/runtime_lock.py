#!/usr/bin/env python3
"""The kernel runtime's hash-locked requirements (eukhe-runtime/requirements-kernel.txt).

The kernel venv bootstrap installs this export of `eukhe-runtime/uv.lock`
with `uv pip install --require-hashes --only-binary :all:`, then the runtime
itself with `--no-deps --no-index --no-build-isolation`. This module is the
offline gate over that file: every entry is an exact `name==version` pin
carrying sha256 hashes (no editable, path, URL, or option lines that could
point uv at an unpinned source), and — with `uv.lock` beside it — every pin
and its hash set match the lock exactly.

Usage:
    python3 scripts/release/runtime_lock.py check [--runtime-dir <dir>]

`make runtime-lock` regenerates the export (`uv lock` + `uv export`, the
runtime's dependencies plus its `kernel` group, without the project itself);
`make runtime-lock-check` re-exports with `--frozen` (offline), diffs, and
runs this module's tests.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

RUNTIME_LOCK_FILE = "requirements-kernel.txt"

_PIN_RE = re.compile(r"^(?P<name>[A-Za-z0-9][A-Za-z0-9._-]*)==(?P<version>[A-Za-z0-9.+!_-]+)$")
_HASH_RE = re.compile(r"^--hash=sha256:(?P<digest>[0-9a-f]{64})$")


class LockError(ValueError):
    """The requirements file is not a fully hash-pinned lock."""


def normalize_name(name: str) -> str:
    return re.sub(r"[-_.]+", "-", name).lower()


def _logical_lines(text: str) -> list[str]:
    lines: list[str] = []
    pending = ""
    for raw in text.splitlines():
        stripped = raw.strip()
        if not pending and (not stripped or stripped.startswith("#")):
            continue
        if stripped.endswith("\\"):
            pending += stripped[:-1] + " "
            continue
        lines.append((pending + stripped).strip())
        pending = ""
    if pending:
        lines.append(pending.strip())
    return lines


def parse_requirements(text: str) -> dict[tuple[str, str], frozenset[str]]:
    """Map each (normalized distribution name, exact version) to its sha256
    digests — a distribution may appear once per marker-selected version —
    and raise LockError on any entry that is not an exact, hashed pin."""
    pins: dict[tuple[str, str], frozenset[str]] = {}
    for line in _logical_lines(text):
        requirement, _, options = line.partition(" --")
        options = ("--" + options).split() if options else []
        spec = requirement.split(";", 1)[0].strip()
        match = _PIN_RE.match(spec)
        if match is None:
            raise LockError(f"not an exact `name==version` pin: {line!r}")
        digests = set()
        for option in options:
            hashed = _HASH_RE.match(option)
            if hashed is None:
                raise LockError(f"unexpected option {option!r} in {line!r}")
            digests.add(hashed["digest"])
        if not digests:
            raise LockError(f"pin without sha256 hashes: {spec!r}")
        key = (normalize_name(match["name"]), match["version"])
        if key in pins:
            raise LockError(f"duplicate pin {key[0]}=={key[1]}")
        pins[key] = frozenset(digests)
    if not pins:
        raise LockError("no pinned requirements")
    return pins


def read_runtime_lock(runtime_dir: Path) -> dict[tuple[str, str], frozenset[str]]:
    path = runtime_dir / RUNTIME_LOCK_FILE
    if not path.is_file():
        raise LockError(f"{path} is missing (run `make runtime-lock`)")
    return parse_requirements(path.read_text(encoding="utf-8"))


def check_against_uv_lock(runtime_dir: Path) -> None:
    """Every exported pin names a locked version and carries exactly the
    lock's artifact hashes for it."""
    import tomllib  # Python >= 3.11; only the source-tree gate needs it.

    pins = read_runtime_lock(runtime_dir)
    lock = tomllib.loads((runtime_dir / "uv.lock").read_text(encoding="utf-8"))
    locked: dict[tuple[str, str], frozenset[str]] = {}
    for package in lock.get("package", []):
        artifacts = list(package.get("wheels", []))
        if "sdist" in package:
            artifacts.append(package["sdist"])
        locked[(normalize_name(package["name"]), package["version"])] = frozenset(
            artifact["hash"].removeprefix("sha256:") for artifact in artifacts
        )
    for (name, version), digests in sorted(pins.items()):
        expected = locked.get((name, version))
        if expected is None:
            raise LockError(f"{name}=={version} is not in uv.lock")
        if digests != expected:
            raise LockError(f"{name}=={version} hashes differ from uv.lock")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check"])
    parser.add_argument(
        "--runtime-dir", type=Path,
        default=Path(__file__).resolve().parents[2] / "eukhe-runtime",
    )
    args = parser.parse_args()
    try:
        check_against_uv_lock(args.runtime_dir)
    except LockError as error:
        print(f"runtime lock check failed: {error}", file=sys.stderr)
        return 1
    print(f"{args.runtime_dir / RUNTIME_LOCK_FILE}: hash-pinned and matches uv.lock")
    return 0


if __name__ == "__main__":
    sys.exit(main())
