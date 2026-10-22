#!/usr/bin/env python3
"""Map a staged change's files to the crates that the pre-commit clippy checks.

scripts/ci_local.sh `clippy_touched` (the pre-commit gate, `make ci-fast`)
runs clippy on the selection: the touched crates and their reverse
dependencies. The mapping is fail-safe by construction: a selection that
cannot be made is the FULL selection (the workspace). A wrong guess can
only cost time, never coverage.

The input is one TSV row per file: `<path>` TAB `<old path>` (the old path
of a rename or copy; empty for ordinary rows). ci_local.sh makes the rows
from `git diff --cached --name-status -M`.

The output is `crates` (a comma list, empty for the full selection) and
`scope` (the human-readable decision), written to the file in
`GITHUB_OUTPUT` (a plain report otherwise), plus a per-path report on stdout.

Usage (scripts/ci_local.sh):

    GITHUB_OUTPUT="${out}" python3 scripts/ci_pr_crates.py <<<"${rows}"

Tests: python3 scripts/test_ci_pr_crates.py
"""

from __future__ import annotations

import os
import sys
from pathlib import Path


# Conservative impact graph: some edges cover behavior beyond a direct
# Cargo.toml link. Over-selecting is safe; missing a dependent is not.
# The selection runs without Cargo.
WORKSPACE_DEPS = {
    "eukhe-types": set(),
    "eukhe-build-info": set(),
    "eukhe-chord": set(),
    "eukhe-ai": {"eukhe-types", "eukhe-chord"},
    "eukhe-durable": {"eukhe-types", "eukhe-chord", "eukhe-ai"},
    "eukhe-models": {"eukhe-types", "eukhe-ai"},
    "eukhe-docs": set(),
    "eukhe-core": {"eukhe-types", "eukhe-chord", "eukhe-ai", "eukhe-durable",
                   "eukhe-models", "eukhe-docs"},
    "eukhe-daemon": {"eukhe-build-info", "eukhe-core", "eukhe-durable", "eukhe-ai",
                     "eukhe-chord"},
    "eukhe-tui": {"eukhe-types", "eukhe-build-info", "eukhe-core"},
    "eukhe-gateway": {"eukhe-types", "eukhe-tui"},
    "eukhe-cli": {"eukhe-types", "eukhe-build-info", "eukhe-chord", "eukhe-ai",
                  "eukhe-durable", "eukhe-models", "eukhe-docs", "eukhe-core", "eukhe-daemon",
                  "eukhe-tui", "eukhe-gateway"},
}


def read_rows(path: Path) -> list[tuple[str, str]]:
    """The change rows, read raw: a leading-space path (` crates/...`)
    must stay the non-crate path it is, never be stripped into a crate
    mapping. The fields are tab-separated, so no strip is needed or safe."""
    rows: list[tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        name, _, previous = line.partition("\t")
        rows.append((name, previous))
    return rows


def select_crates(rows: list[tuple[str, str]]) -> list[str] | None:
    """The touched crates and reverse dependencies, or None for the full
    selection.

    Only known `crates/<pkg>/**` narrows. Everything else (the workflow,
    CI tooling, vendor/, the runtime sidecar, workspace-level Cargo files,
    install scripts, docs) affects more than any crate subset, and a rename
    counts both sides. An undecidable list (empty rows, an empty path or an
    unknown crate) fails safe to the full selection.
    """
    if not rows:
        return None
    crates: set[str] = set()
    for name, previous in rows:
        if not name:
            # An empty path column means the input is not the row shape:
            # never select from it.
            print("an empty filename in the change list: the full selection runs")
            return None
        for candidate in (name, previous):
            if not candidate:
                continue  # an ordinary (non-rename) row has no removed side
            parts = candidate.split("/")
            if len(parts) >= 2 and parts[0] == "crates" and parts[1]:
                if parts[1] not in WORKSPACE_DEPS:
                    print(f"unknown crate {parts[1]}: the full selection runs")
                    return None
                crates.add(parts[1])
            else:
                print(f"non-crate path {candidate}: the full selection runs")
                return None
    # eukhe-types owns the shared wire vocabulary: select every crate for its
    # changes.
    if "eukhe-types" in crates:
        return sorted(WORKSPACE_DEPS)
    # Walk upward through the DAG until no dependent is left unselected.
    while True:
        dependents = {crate for crate, deps in WORKSPACE_DEPS.items()
                      if deps & crates}
        expanded = crates | dependents
        if expanded == crates:
            return sorted(crates)
        crates = expanded


def write_outputs(crates: list[str] | None, output_path: str) -> None:
    lines = []
    if crates is None:
        lines.append("crates=")
        lines.append("scope=all")
    else:
        lines.append("crates=" + ",".join(crates))
        lines.append(f"scope=crates ({len(crates)}: {', '.join(crates)})")
    if output_path and output_path != "/dev/null":
        with open(output_path, "a", encoding="utf-8") as handle:
            handle.write("\n".join(lines) + "\n")
    print("selection: " + lines[1].removeprefix("scope="))
    if crates:
        print("crates selected: " + ",".join(crates))


def main() -> int:
    rows = read_rows(Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/dev/stdin"))
    crates = select_crates(rows)
    write_outputs(crates, os.environ.get("GITHUB_OUTPUT", "/dev/null"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
