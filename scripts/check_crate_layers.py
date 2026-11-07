#!/usr/bin/env python3
"""Check the crate layering of AGENTS.md (Crates) on the workspace manifests.

Two rules, over every dependency kind (normal, build, dev):

- No crate outside the frontends (`eukhe-tui`, `eukhe-cli`,
  `eukhe-dashboard`, `eukhe-gateway`) depends on a frontend: the engine and
  the client never reach up into a UI.
- The daemon-wire side (`eukhe-client` and the frontends that talk to the
  daemon through it: `eukhe-tui`, `eukhe-dashboard`, `eukhe-gateway`) never
  links the session engine (`eukhe-core`, `eukhe-daemon`, `eukhe-durable`),
  directly or through another workspace crate.

The graph comes from `cargo metadata --no-deps` (no build, no network).
Prints each violation and exits 1, else prints a summary and exits 0.

Usage (scripts/ci_local.sh): python3 scripts/check_crate_layers.py .

Tests: python3 scripts/test_check_crate_layers.py
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

FRONTENDS = frozenset({"eukhe-tui", "eukhe-cli", "eukhe-dashboard", "eukhe-gateway"})
WIRE_SIDE = frozenset({"eukhe-client", "eukhe-tui", "eukhe-dashboard", "eukhe-gateway"})
ENGINE = frozenset({"eukhe-core", "eukhe-daemon", "eukhe-durable"})

# A workspace crate's workspace dependencies: name -> {(dependency, kind)},
# kind one of "normal", "build", "dev".
Graph = dict[str, set[tuple[str, str]]]


def graph_of(metadata: dict) -> Graph:
    """The workspace dependency graph of a `cargo metadata` document."""
    members = {package["name"] for package in metadata["packages"]}
    return {
        package["name"]: {
            (dependency["name"], dependency["kind"] or "normal")
            for dependency in package["dependencies"]
            if dependency["name"] in members
        }
        for package in metadata["packages"]
    }


def linked(graph: Graph, crate: str) -> dict[str, list[str]]:
    """Every workspace crate `crate` links, with the path that links it.
    The crate's own dev dependencies count (its tests link them); a
    dependency's dev dependencies do not."""
    paths: dict[str, list[str]] = {}
    frontier = [(name, [crate, name]) for name, _ in sorted(graph.get(crate, set()))]
    while frontier:
        name, path = frontier.pop(0)
        if name in paths or name == crate:
            continue
        paths[name] = path
        frontier.extend(
            (dependency, [*path, dependency])
            for dependency, kind in sorted(graph.get(name, set()))
            if kind != "dev"
        )
    return paths


def violations(graph: Graph) -> list[str]:
    """The layering violations of `graph`, one line each, sorted."""
    found = []
    for crate, dependencies in graph.items():
        if crate in FRONTENDS:
            continue
        for dependency, kind in dependencies:
            if dependency in FRONTENDS:
                found.append(f"{crate} -> {dependency} ({kind}): only a frontend depends on a frontend")
    for crate in WIRE_SIDE & graph.keys():
        for engine, path in linked(graph, crate).items():
            if engine in ENGINE:
                found.append(f"{' -> '.join(path)}: {crate} is on the daemon-wire side; it never links {engine}")
    return sorted(found)


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    metadata = subprocess.run(
        ["cargo", "metadata", "--format-version", "1", "--no-deps", "--locked"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    graph = graph_of(json.loads(metadata))
    found = violations(graph)
    for line in found:
        print(line, file=sys.stderr)
    if found:
        return 1
    print(f"crate layers OK ({len(graph)} crates)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
