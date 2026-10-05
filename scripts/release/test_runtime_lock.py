#!/usr/bin/env python3
"""Offline gates for the kernel runtime's hash-locked requirements."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from runtime_lock import (  # noqa: E402
    LockError,
    check_against_uv_lock,
    parse_requirements,
)

REPO_RUNTIME = Path(__file__).resolve().parents[2] / "eukhe-runtime"
DIGEST_A = "a" * 64
DIGEST_B = "b" * 64


class ParseRequirements(unittest.TestCase):
    def test_hashed_pins_parse_with_markers_and_comments(self) -> None:
        text = (
            "# header\n"
            f"Dill==0.4.1 \\\n    --hash=sha256:{DIGEST_A} \\\n    --hash=sha256:{DIGEST_B}\n"
            "    # via eukhe-runtime\n"
            f"colorama==0.4.6 ; sys_platform == 'win32' \\\n    --hash=sha256:{DIGEST_A}\n"
        )
        self.assertEqual(
            parse_requirements(text),
            {
                ("dill", "0.4.1"): frozenset({DIGEST_A, DIGEST_B}),
                ("colorama", "0.4.6"): frozenset({DIGEST_A}),
            },
        )

    def test_entries_an_index_could_resolve_are_rejected(self) -> None:
        for text, message in (
            (f"dill>=0.4 --hash=sha256:{DIGEST_A}\n", "not an exact `name==version` pin: 'dill>=0.4 --hash=sha256:" + DIGEST_A + "'"),
            ("dill==0.4.1\n", "pin without sha256 hashes: 'dill==0.4.1'"),
            ("-e .\n", "not an exact `name==version` pin: '-e .'"),
            (f"eukhe-runtime @ file:///x --hash=sha256:{DIGEST_A}\n",
             f"not an exact `name==version` pin: 'eukhe-runtime @ file:///x --hash=sha256:{DIGEST_A}'"),
            (f"dill==0.4.1 --index-url https://example.invalid --hash=sha256:{DIGEST_A}\n",
             f"unexpected option '--index-url' in 'dill==0.4.1 --index-url https://example.invalid --hash=sha256:{DIGEST_A}'"),
            ("# only comments\n", "no pinned requirements"),
        ):
            with self.subTest(text=text):
                with self.assertRaises(LockError) as caught:
                    parse_requirements(text)
                self.assertEqual(str(caught.exception), message)


class UvLockParity(unittest.TestCase):
    def test_committed_export_matches_uv_lock(self) -> None:
        check_against_uv_lock(REPO_RUNTIME)

    def test_hash_drift_from_uv_lock_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp)
            (runtime / "uv.lock").write_text(
                'version = 1\n[[package]]\nname = "dill"\nversion = "0.4.1"\n'
                f'wheels = [{{ url = "https://x/dill.whl", hash = "sha256:{DIGEST_A}" }}]\n'
            )
            (runtime / "requirements-kernel.txt").write_text(
                f"dill==0.4.1 --hash=sha256:{DIGEST_B}\n"
            )
            with self.assertRaises(LockError) as caught:
                check_against_uv_lock(runtime)
            self.assertEqual(str(caught.exception), "dill==0.4.1 hashes differ from uv.lock")


if __name__ == "__main__":
    unittest.main()
