#!/usr/bin/env python3
"""Tests for the next-release rule (next_version.py) and its bridge to the
Bend model (bend/semver.bend, laws/semver.bend, R1).

The bridge builds bend/bridge_semver.bend into a native binary (needs
`bend` 2.0.38, from $BEND or PATH, and clang), runs it on generated cases
and requires its transcript to equal the script's, byte for byte. Without
`bend` the bridge is skipped with a message, unless EUKHE_REQUIRE_BEND is
set (as CI sets it): then a missing `bend` fails it.

Run: python3 scripts/release/test_next_version.py
"""

from __future__ import annotations

import io
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import next_version  # noqa: E402  (same release-scripts directory)

ROOT = Path(__file__).resolve().parents[2]
BRIDGE = ROOT / "bend" / "bridge_semver.bend"


def run_main(workspace: str, tags: list[str]) -> tuple[int, str, str]:
    stdout, stderr = io.StringIO(), io.StringIO()
    stdin = io.StringIO("".join(f"{tag}\n" for tag in tags))
    with mock.patch.object(sys, "stdin", stdin), redirect_stdout(stdout), redirect_stderr(stderr):
        code = next_version.main(["--workspace-version", workspace])
    return code, stdout.getvalue(), stderr.getvalue()


class RuleTest(unittest.TestCase):
    def test_the_first_release_of_a_series_is_patch_zero(self):
        self.assertEqual(
            run_main("0.10.0", ["v0.9.9", "eukhe-v0.9.9-main.47", "eukhe-v0.9.12"]),
            (0, "version=0.10.0\ntag=eukhe-v0.10.0\ntitle=Eukhe v0.10.0\n", ""),
        )

    def test_each_release_takes_one_more_than_the_highest_patch(self):
        tags = ["eukhe-v0.10.0", "eukhe-v0.10.7", "eukhe-v0.10.3", "v0.10.99", "eukhe-v0.10.08"]
        self.assertEqual(
            run_main("0.10.0", tags),
            (0, "version=0.10.8\ntag=eukhe-v0.10.8\ntitle=Eukhe v0.10.8\n", ""),
        )

    def test_a_new_series_starts_at_zero_above_the_older_series(self):
        self.assertEqual(next_version.release("0.11.0", ["eukhe-v0.10.39"]), (0, 11, 0))
        self.assertEqual(next_version.release("1.0.0", ["eukhe-v0.10.39", "eukhe-v0.11.4"]), (1, 0, 0))

    def test_a_workspace_version_that_is_no_series_fails(self):
        for workspace in ["0.10.1", "0.10.0-dev", "0.010.0", "1.2", ""]:
            with self.subTest(workspace=workspace):
                code, out, err = run_main(workspace, [])
                self.assertEqual((code, out), (1, ""))
                self.assertTrue(err.startswith("error: the workspace version"), err)

    def test_a_tag_of_a_newer_series_fails(self):
        self.assertEqual(
            run_main("0.10.0", ["eukhe-v0.10.2", "eukhe-v0.11.0"]),
            (
                1,
                "",
                "error: the next release 0.10.3 is not newer than the tag(s) eukhe-v0.11.0: "
                "move the workspace version to a newer series\n",
            ),
        )

    def test_versions_are_canonical_decimal(self):
        cases = {
            "0.10.0": (0, 10, 0),
            "12.0.109": (12, 0, 109),
            "01.2.3": None,
            "1.2.03": None,
            "1.2": None,
            "1.2.3.4": None,
            "1..3": None,
            "1.2.3-dev": None,
            "+1.2.3": None,
            "1.2.3\n": None,
            "١.2.3": None,
        }
        self.assertEqual({text: next_version.parse(text) for text in cases}, cases)

    def test_the_workspace_version_is_read_from_cargo_toml(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "Cargo.toml"
            manifest.write_text('[package]\nversion = "9.9.9"\n\n[workspace.package]\nversion = "0.10.0"\n')
            self.assertEqual(next_version.workspace_version(manifest), "0.10.0")


# The bridge
# ----------

NAMES = ["eukhe-v", "v", "eukhe-", "eukhe-v0.9.9-main.", "Eukhe v", ""]


def number(rng: random.Random) -> str:
    """A field: mostly a small number, sometimes not canonical."""
    roll = rng.random()
    if roll < 0.80:
        return str(rng.choice([0, 0, 1, 2, 3, 9, 10, 11, 19, 20, 39, 40]))
    if roll < 0.88:
        return "0" + str(rng.randrange(0, 12))
    return rng.choice(["", "x", "1a", "-1", "+1", " 1"])


def version_text(rng: random.Random) -> str:
    fields = [number(rng) for _ in range(rng.choice([3, 3, 3, 3, 3, 2, 4]))]
    text = ".".join(fields)
    if rng.random() < 0.05:
        text += rng.choice(["-dev", ".", " ", "-main.4"])
    return text


def tag(rng: random.Random, series: tuple[str, str]) -> str:
    roll = rng.random()
    if roll < 0.55:
        return f"eukhe-v{series[0]}.{series[1]}.{rng.randrange(0, 41)}"
    if roll < 0.85:
        return rng.choice(NAMES) + version_text(rng)
    return f"eukhe-v{rng.choice(['0', '1'])}.{rng.randrange(0, 13)}.{rng.randrange(0, 41)}"


def workspace(rng: random.Random) -> tuple[str, tuple[str, str]]:
    major, minor = rng.choice(["0", "1"]), str(rng.randrange(0, 13))
    roll = rng.random()
    if roll < 0.75:
        return f"{major}.{minor}.0", (major, minor)
    if roll < 0.85:
        return f"{major}.{minor}.{rng.randrange(1, 5)}", (major, minor)
    return version_text(rng), (major, minor)


def cases() -> list[tuple[str, list[str]]]:
    rng = random.Random(0x5E5E_0001)
    generated = [
        ("0.10.0", []),
        ("0.10.0", ["eukhe-v0.10.0"]),
        ("0.11.0", ["eukhe-v0.10.39", "v0.11.0"]),
        ("0.10.0", ["eukhe-v0.11.0"]),
        ("0.10.1", ["eukhe-v0.10.0"]),
        ("", ["eukhe-v0.10.0"]),
        ("0.10.0", ["", "eukhe-v", "eukhe-v0.10.07", "eukhe-v0.10.3.1"]),
    ]
    for _ in range(400):
        current, series = workspace(rng)
        generated.append((current, [tag(rng, series) for _ in range(rng.randrange(0, 9))]))
    return generated


def script_transcript(generated: list[tuple[str, list[str]]]) -> tuple[str, set[str]]:
    lines, reached = [], set()
    for current, tags in generated:
        series = next_version.parse(current)
        if series is None:
            lines.append("next -")
        else:
            lines.append(f"next {next_version.show(next_version.next_in_series(series, tags))}")
        try:
            version = next_version.release(current, tags)
        except next_version.ReleaseError as error:
            lines.append("release -")
            reached.add(str(error).split(" ", 3)[2])
            continue
        shown = next_version.show(version)
        lines.append(f"release eukhe-v{shown} Eukhe v{shown}")
        reached.add("fresh" if version[2] == 0 else "next")
    return "".join(f"{line}\n" for line in lines), reached


def bend_binary() -> str | None:
    return os.environ.get("BEND") or shutil.which("bend")


class BridgeTest(unittest.TestCase):
    def test_the_script_equals_the_bend_model(self):
        generated = cases()
        transcript, reached = script_transcript(generated)
        # The cases reach every outcome: a fresh series, a next patch, a
        # workspace version that is no version or no series, a newer tag.
        self.assertEqual(reached, {"fresh", "next", "version", "release"})
        bend = bend_binary()
        if bend is None:
            self.assertNotIn(
                "EUKHE_REQUIRE_BEND",
                os.environ,
                "EUKHE_REQUIRE_BEND is set but no `bend` is on PATH (or in $BEND)",
            )
            self.skipTest("`bend` is not installed (version 2.0.38): the script was not compared with bend/semver.bend")
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "bridge_semver"
            built = subprocess.run([bend, str(BRIDGE), "-o", str(binary)], capture_output=True, text=True)
            self.assertEqual(built.returncode, 0, f"bend could not build {BRIDGE}:\n{built.stdout}{built.stderr}")
            scenario = Path(tmp) / "scenario"
            scenario.write_text("".join("\t".join(["case", current, *tags]) + "\n" for current, tags in generated))
            ran = subprocess.run([str(binary), str(scenario)], capture_output=True, text=True, check=False)
            self.assertEqual(ran.returncode, 0, ran.stderr)
            self.assertEqual(ran.stdout, transcript)


if __name__ == "__main__":
    unittest.main()
