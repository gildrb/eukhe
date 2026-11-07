#!/usr/bin/env python3
"""Tests of check_crate_layers.py: each rule fails on a graph that breaks it.

Run: python3 scripts/test_check_crate_layers.py
"""

from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_crate_layers import graph_of, violations  # noqa: E402  (the tool under test)

ROOT = Path(__file__).resolve().parent.parent

# The layering of AGENTS.md, reduced.
LAYERED = {
    "eukhe-types": set(),
    "eukhe-durable": {("eukhe-types", "normal")},
    "eukhe-core": {("eukhe-durable", "normal")},
    "eukhe-daemon": {("eukhe-core", "normal"), ("eukhe-durable", "dev")},
    "eukhe-sdk": {("eukhe-core", "normal")},
    "eukhe-client": {("eukhe-types", "normal")},
    "eukhe-tui": {("eukhe-client", "normal")},
    "eukhe-dashboard": {("eukhe-client", "normal")},
    "eukhe-gateway": {("eukhe-client", "normal"), ("eukhe-tui", "normal")},
    "eukhe-cli": {("eukhe-daemon", "normal"), ("eukhe-tui", "normal"), ("eukhe-core", "normal")},
}


def with_edges(**extra: set[tuple[str, str]]) -> dict[str, set[tuple[str, str]]]:
    graph = {crate: set(dependencies) for crate, dependencies in LAYERED.items()}
    for crate, dependencies in extra.items():
        graph.setdefault(crate.replace("_", "-"), set()).update(dependencies)
    return graph


class LayersTestCase(unittest.TestCase):
    def test_the_layering_passes(self) -> None:
        self.assertEqual(violations(LAYERED), [])

    def test_an_engine_crate_on_a_frontend_fails(self) -> None:
        self.assertEqual(
            violations(with_edges(eukhe_core={("eukhe-tui", "normal")})),
            ["eukhe-core -> eukhe-tui (normal): only a frontend depends on a frontend"],
        )

    def test_an_engine_dev_dependency_on_a_frontend_fails(self) -> None:
        self.assertEqual(
            violations(with_edges(eukhe_daemon={("eukhe-cli", "dev")})),
            ["eukhe-daemon -> eukhe-cli (dev): only a frontend depends on a frontend"],
        )

    def test_the_client_on_a_frontend_fails(self) -> None:
        self.assertEqual(
            violations(with_edges(eukhe_client={("eukhe-gateway", "normal")})),
            ["eukhe-client -> eukhe-gateway (normal): only a frontend depends on a frontend"],
        )

    def test_the_client_linking_the_engine_fails_every_crate_on_it(self) -> None:
        self.assertEqual(
            violations(with_edges(eukhe_client={("eukhe-durable", "normal")})),
            [
                "eukhe-client -> eukhe-durable: eukhe-client is on the daemon-wire side; it never links eukhe-durable",
                "eukhe-dashboard -> eukhe-client -> eukhe-durable: eukhe-dashboard is on the daemon-wire side; it never links eukhe-durable",
                "eukhe-gateway -> eukhe-client -> eukhe-durable: eukhe-gateway is on the daemon-wire side; it never links eukhe-durable",
                "eukhe-tui -> eukhe-client -> eukhe-durable: eukhe-tui is on the daemon-wire side; it never links eukhe-durable",
            ],
        )

    def test_a_frontend_linking_the_engine_through_another_crate_fails(self) -> None:
        self.assertEqual(
            violations(with_edges(eukhe_dashboard={("eukhe-sdk", "build")})),
            [
                "eukhe-dashboard -> eukhe-sdk -> eukhe-core -> eukhe-durable: eukhe-dashboard is on the daemon-wire side; it never links eukhe-durable",
                "eukhe-dashboard -> eukhe-sdk -> eukhe-core: eukhe-dashboard is on the daemon-wire side; it never links eukhe-core",
            ],
        )

    def test_a_dependencys_dev_dependency_is_not_linked(self) -> None:
        graph = with_edges(eukhe_types={("eukhe-core", "dev")})
        self.assertEqual(violations(graph), [])

    def test_the_metadata_graph_keeps_workspace_edges_and_kinds(self) -> None:
        metadata = {"packages": [
            {"name": "eukhe-a", "dependencies": [
                {"name": "eukhe-b", "kind": None},
                {"name": "eukhe-b", "kind": "dev"},
                {"name": "serde", "kind": None},
            ]},
            {"name": "eukhe-b", "dependencies": [{"name": "eukhe-a", "kind": "build"}]},
        ]}
        self.assertEqual(graph_of(metadata), {
            "eukhe-a": {("eukhe-b", "normal"), ("eukhe-b", "dev")},
            "eukhe-b": {("eukhe-a", "build")},
        })

    def test_this_workspace_passes(self) -> None:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "check_crate_layers.py"), str(ROOT)],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual((result.returncode, result.stderr), (0, ""), result.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
