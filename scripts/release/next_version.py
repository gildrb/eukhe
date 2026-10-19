#!/usr/bin/env python3
"""The version of the next eukhe release (the model: bend/semver.bend).

Usage: next_version.py [--workspace-version X.Y.Z] < tags

Reads the repository's tag names on stdin, one per line, and prints the
release's version, tag and title as `key=value` lines (GITHUB_OUTPUT
format):

    version=0.10.4
    tag=eukhe-v0.10.4
    title=Eukhe v0.10.4

The rule:
- A version is major.minor.patch, each a decimal number without leading
  zeros ("0", "7", "10"; never "", "07", "+7"), and nothing else.
- The series is the workspace version of Cargo.toml ([workspace.package]
  version, or --workspace-version), which must be X.Y.0.
- The next release is X.Y.P: P is 1 + the highest patch among the tags
  `eukhe-v<X>.<Y>.<P>`, 0 when there is none. Every other tag (other
  series, the upstream `v*` tags, `eukhe-v0.9.9-main.4`) does not count.
- The release must be newer than every version tag, of any series (a tag
  of a newer series means Cargo.toml went back): else it fails.

laws/release.bend (section R1) states the rule's laws; test_next_version.py runs
this script and the Bend model on the same cases.
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TAG_PREFIX = "eukhe-v"
TITLE_PREFIX = "Eukhe v"
NUMBER = r"(0|[1-9][0-9]*)"
VERSION = re.compile(rf"{NUMBER}\.{NUMBER}\.{NUMBER}")

Version = tuple[int, int, int]


class ReleaseError(Exception):
    """The commit has no release (the message says why)."""


def parse(text: str) -> Version | None:
    """The version `text` names, None for any other text."""
    match = VERSION.fullmatch(text)
    if match is None:
        return None
    major, minor, patch = (int(field) for field in match.groups())
    return (major, minor, patch)


def show(version: Version) -> str:
    return ".".join(str(field) for field in version)


def tag_version(tag: str) -> Version | None:
    """The version a tag names (`eukhe-v` + version), None for any other."""
    if not tag.startswith(TAG_PREFIX):
        return None
    return parse(tag[len(TAG_PREFIX):])


def next_in_series(series: Version, tags: list[str]) -> Version:
    """X.Y.P: 1 + the highest patch among the series' tags, 0 when none."""
    major, minor, _ = series
    patches = [
        version[2]
        for version in map(tag_version, tags)
        if version is not None and version[:2] == (major, minor)
    ]
    return (major, minor, max(patches) + 1 if patches else 0)


def release(workspace_version: str, tags: list[str]) -> Version:
    """The release of a commit with this workspace version and these tags."""
    series = parse(workspace_version)
    if series is None:
        raise ReleaseError(
            f"the workspace version {workspace_version!r} is not major.minor.patch"
        )
    if series[2] != 0:
        raise ReleaseError(
            f"the workspace version {workspace_version} names a series: it must be "
            f"{series[0]}.{series[1]}.0 (each release takes the next patch)"
        )
    version = next_in_series(series, tags)
    newer = sorted(
        tag for tag in tags if (named := tag_version(tag)) is not None and named >= version
    )
    if newer:
        raise ReleaseError(
            f"the next release {show(version)} is not newer than the tag(s) "
            f"{', '.join(newer)}: move the workspace version to a newer series"
        )
    return version


def workspace_version(manifest: Path) -> str:
    with manifest.open("rb") as handle:
        return tomllib.load(handle)["workspace"]["package"]["version"]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--workspace-version",
        help="the series X.Y.0 (default: [workspace.package] version of Cargo.toml)",
    )
    args = parser.parse_args(argv)
    current = (
        workspace_version(ROOT / "Cargo.toml")
        if args.workspace_version is None
        else args.workspace_version
    )
    tags = [line for line in sys.stdin.read().split("\n") if line]
    try:
        version = release(current, tags)
    except ReleaseError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"version={show(version)}")
    print(f"tag={TAG_PREFIX}{show(version)}")
    print(f"title={TITLE_PREFIX}{show(version)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
