#!/usr/bin/env python3
"""Set the workspace version in Cargo.toml (rolling main releases).

Usage: stamp_version.py <version>

Replaces `version = "..."` under `[workspace.package]`. Every crate inherits
it, so the binary, the daemon build id, and `--version` report the release.
Run `cargo update --workspace` afterwards to move Cargo.lock with it.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SEMVER = re.compile(r"^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?$")
SECTION = re.compile(r"^\[workspace\.package\]\s*$", re.MULTILINE)
VERSION_LINE = re.compile(r'^version\s*=\s*"[^"]*"\s*$', re.MULTILINE)


def stamp(text: str, version: str) -> str:
    section = SECTION.search(text)
    if section is None:
        raise SystemExit("error: Cargo.toml has no [workspace.package] section")
    next_section = re.compile(r"^\[", re.MULTILINE).search(text, section.end())
    end = next_section.start() if next_section else len(text)
    body = text[section.end():end]
    line = VERSION_LINE.search(body)
    if line is None:
        raise SystemExit("error: [workspace.package] has no version line")
    start = section.end() + line.start()
    stop = section.end() + line.end()
    return f'{text[:start]}version = "{version}"{text[stop:]}'


def main(argv: list[str]) -> int:
    if len(argv) != 1 or SEMVER.match(argv[0]) is None:
        raise SystemExit("usage: stamp_version.py <semver version>")
    manifest = ROOT / "Cargo.toml"
    manifest.write_text(stamp(manifest.read_text(), argv[0]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
