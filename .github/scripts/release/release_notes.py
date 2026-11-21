#!/usr/bin/env python3
"""The notes of an eukhe release: what changed since the previous release.

Usage: release_notes.py --version X.Y.P --sha <commit> [--previous <tag>] < subjects

Reads the first-parent commit subjects since the previous release on
stdin, newest first, one per line (`git log --first-parent --format=%s
<previous>..<sha>`), and prints the release body as Markdown.

The rule, deterministic from the subjects alone (no model call):
- A subject `area: change` belongs to its area, in lower case; one
  without a colon belongs to the area "other". The area is the text
  before the first `: `.
- Internal areas are left out, by the area's first word: ci, ci-local,
  ci-fast, docs, nix, make, agents, laws, tests, test, runtime, chore,
  release. A subject `nix: release.json for ...` is the release
  bookkeeping commit.
- Areas are listed in the order of their newest change; inside an area
  the changes keep the log order (newest first). Each change is the
  subject's text after the area, unchanged.
- A release with no user-facing change says so.
"""

from __future__ import annotations

import argparse
import sys

INTERNAL_AREAS = frozenset(
    {
        "agents",
        "chore",
        "ci",
        "ci-fast",
        "ci-local",
        "docs",
        "laws",
        "make",
        "nix",
        "release",
        "runtime",
        "test",
        "tests",
    }
)
OTHER = "other"


def split_subject(subject: str) -> tuple[str, str]:
    """The (area, change) of one subject."""
    area, separator, change = subject.partition(": ")
    if not separator or not area.strip() or not change.strip():
        return OTHER, subject.strip()
    return area.strip().lower(), change.strip()


def group(subjects: list[str]) -> list[tuple[str, list[str]]]:
    """The user-facing changes grouped by area, areas in order of their
    newest change."""
    groups: dict[str, list[str]] = {}
    for subject in subjects:
        if not subject.strip():
            continue
        area, change = split_subject(subject)
        if area.split()[0] in INTERNAL_AREAS:
            continue
        groups.setdefault(area, []).append(change)
    return list(groups.items())


def render(version: str, sha: str, previous: str | None, subjects: list[str]) -> str:
    lines = [f"eukhe {version}, built from {sha}; the full gate passed on it.", ""]
    since = f" since {previous}" if previous else ""
    groups = group(subjects)
    if not groups:
        lines.append(f"No user-facing change{since}.")
    else:
        lines.append(f"## Changes{since}")
        lines.append("")
        for area, changes in groups:
            for change in changes:
                lines.append(f"- **{area}**: {change}")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--version", required=True)
    parser.add_argument("--sha", required=True)
    parser.add_argument("--previous", default=None)
    args = parser.parse_args()
    subjects = sys.stdin.read().splitlines()
    sys.stdout.write(render(args.version, args.sha, args.previous, subjects))
    return 0


if __name__ == "__main__":
    sys.exit(main())
