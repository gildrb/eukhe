#!/usr/bin/env python3
"""Set the workspace version in Cargo.toml and Cargo.lock (rolling main releases).

Usage: stamp_version.py <version>

Replaces `version = "..."` under `[workspace.package]`. Every crate inherits
it, so the binary, the daemon build id, and `--version` report the release.
Cargo.lock moves with it without a resolver run: only the `version` lines of
the workspace's own `eukhe-*` packages (no `source`) change, and each must
hold the previous workspace version. The release build's `--locked` then
fails if the lockfile needs any other change.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SEMVER = re.compile(r"^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?$")
SECTION = re.compile(r"^\[workspace\.package\]\s*$", re.MULTILINE)
VERSION_LINE = re.compile(r'^version\s*=\s*"([^"]*)"\s*$', re.MULTILINE)
# A workspace package entry: `eukhe-*` name, then version, and no `source`
# line (registry and git packages always carry one).
WORKSPACE_LOCK_ENTRY = re.compile(
    r'(^\[\[package\]\]\nname = "eukhe-[^"]+"\nversion = ")([^"]*)("\n(?!source = ))',
    re.MULTILINE,
)


def version_line(text: str) -> re.Match:
    """The `version = "..."` line of [workspace.package], with absolute
    offsets."""
    section = SECTION.search(text)
    if section is None:
        raise SystemExit("error: Cargo.toml has no [workspace.package] section")
    next_section = re.compile(r"^\[", re.MULTILINE).search(text, section.end())
    end = next_section.start() if next_section else len(text)
    line = VERSION_LINE.search(text, section.end(), end)
    if line is None:
        raise SystemExit("error: [workspace.package] has no version line")
    return line


def stamp(text: str, version: str) -> str:
    line = version_line(text)
    return f'{text[:line.start()]}version = "{version}"{text[line.end():]}'


def stamp_lock(text: str, previous: str, version: str) -> str:
    stamped = []

    def replace(entry: re.Match) -> str:
        if entry.group(2) != previous:
            raise SystemExit(
                f"error: Cargo.lock entry {entry.group(0).splitlines()[1]} has "
                f"version {entry.group(2)!r}, expected the workspace version {previous!r}"
            )
        stamped.append(entry.group(0))
        return f"{entry.group(1)}{version}{entry.group(3)}"

    result = WORKSPACE_LOCK_ENTRY.sub(replace, text)
    if not stamped:
        raise SystemExit("error: Cargo.lock has no eukhe-* workspace package entries")
    return result


def main(argv: list[str]) -> int:
    if len(argv) != 1 or SEMVER.match(argv[0]) is None:
        raise SystemExit("usage: stamp_version.py <semver version>")
    manifest = ROOT / "Cargo.toml"
    lockfile = ROOT / "Cargo.lock"
    manifest_text = manifest.read_text()
    previous = version_line(manifest_text).group(1)
    lock_text = stamp_lock(lockfile.read_text(), previous, argv[0])
    manifest.write_text(stamp(manifest_text, argv[0]))
    lockfile.write_text(lock_text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
