#!/usr/bin/env python3
"""nix/merge-settings.sh, the Home Manager activation of
`programs.eukhe.settings`: the declared settings merge into
~/.eukhe/settings.json and never drop what eukhe wrote there (the saved
model choice). Needs bash and jq on PATH (the module puts jq there)."""
import json
import os
import shutil
import stat
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "merge-settings.sh"


def merge(target: Path, declared: dict) -> subprocess.CompletedProcess:
    source = target.parent.parent / "declared.json"
    source.write_text(json.dumps(declared, sort_keys=True))
    return subprocess.run(
        ["bash", str(SCRIPT), str(target), str(source)],
        capture_output=True,
        text=True,
        check=False,
    )


class MergeSettingsTest(unittest.TestCase):
    def setUp(self) -> None:
        if shutil.which("jq") is None:
            self.fail("jq is not installed (the Home Manager module provides it)")
        self.dir = Path(tempfile.mkdtemp())
        self.target = self.dir / ".eukhe" / "settings.json"

    def tearDown(self) -> None:
        shutil.rmtree(self.dir)

    def test_the_saved_model_choice_survives_an_activation(self) -> None:
        # The regression: the activation installed the declared settings
        # over the file, so every Home Manager switch (an eukhe update)
        # dropped the model the user had chosen and the next session
        # started on the featured default.
        self.target.parent.mkdir()
        self.target.write_text(json.dumps({
            "theme": "old",
            "memory": {"model": "elpis/qwen3.8-27b", "thinking": "low"},
            "defaultProvider": "elpis",
            "defaultModel": "qwen3.8-27b",
            "recentModels": ["elpis/qwen3.8-27b", "anthropic/claude-opus-5-5"],
            "trustedProjects": ["/old"],
        }, indent=2))
        result = merge(self.target, {
            "theme": "death-note",
            "memory": {"model": "anthropic/claude-sonnet-5-5"},
            "trustedProjects": ["/home/u/Repos/dotfiles"],
            "onboardingShown": True,
        })
        self.assertEqual((result.returncode, result.stderr), (0, ""))
        self.assertEqual(json.loads(self.target.read_text()), {
            "theme": "death-note",
            "memory": {"model": "anthropic/claude-sonnet-5-5", "thinking": "low"},
            "defaultProvider": "elpis",
            "defaultModel": "qwen3.8-27b",
            "recentModels": ["elpis/qwen3.8-27b", "anthropic/claude-opus-5-5"],
            "trustedProjects": ["/home/u/Repos/dotfiles"],
            "onboardingShown": True,
        })
        self.assertEqual(stat.S_IMODE(self.target.stat().st_mode), 0o600)
        self.assertFalse(Path(f"{self.target}.lock").exists())

    def test_a_missing_file_becomes_the_declared_settings(self) -> None:
        result = merge(self.target, {"theme": "death-note"})
        self.assertEqual((result.returncode, result.stderr), (0, ""))
        self.assertEqual(json.loads(self.target.read_text()), {"theme": "death-note"})
        self.assertEqual(stat.S_IMODE(self.target.stat().st_mode), 0o600)

    def test_a_file_that_is_not_an_object_is_left_as_it_is(self) -> None:
        self.target.parent.mkdir()
        for content in ['{"defaultModel": "m",', "[1, 2]"]:
            self.target.write_text(content)
            result = merge(self.target, {"theme": "death-note"})
            self.assertEqual(
                (result.returncode, result.stderr, self.target.read_text()),
                (
                    0,
                    f"eukhe: {self.target} is not a JSON object; the declared "
                    "settings were not applied (fix or remove the file)\n",
                    content,
                ),
            )
            self.assertFalse(Path(f"{self.target}.lock").exists())

    def test_a_stale_lock_is_taken_and_released(self) -> None:
        self.target.parent.mkdir()
        self.target.write_text('{"defaultModel": "m"}')
        lock = Path(f"{self.target}.lock")
        lock.mkdir()
        old = time.time() - 60
        os.utime(lock, (old, old))
        result = merge(self.target, {"theme": "t"})
        self.assertEqual((result.returncode, result.stderr), (0, ""))
        self.assertEqual(
            json.loads(self.target.read_text()), {"defaultModel": "m", "theme": "t"}
        )
        self.assertFalse(lock.exists())


if __name__ == "__main__":
    unittest.main()
