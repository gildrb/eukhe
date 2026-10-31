from __future__ import annotations

import asyncio
import importlib.util
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch


SKILL = Path(__file__).parents[2] / "skills/autoresearch/src/autoresearch/__init__.py"


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, SKILL)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _state(**overrides):
    state = {
        "config": {"metric": "time_ms", "max_iterations": 4},
        "segment": 0,
        "mode": "on",
        "pending": None,
        "baseline": "10",
        "best": "8",
        "logged": 2,
        "confidence_tenths": 25,
        "runs": [],
        "runs_in_segment": 2,
        "runs_total": 2,
    }
    state.update(overrides)
    return state


class AutoresearchSkillTest(unittest.TestCase):
    def test_init_sends_the_config(self) -> None:
        module = _load("autoresearch_init")
        host = AsyncMock(return_value={"branch": "b", "git": None, "state": _state()})
        with patch.object(module, "host_request", host):
            asyncio.run(
                module.init("parser", "time_ms", scope=["src"], max_iterations=4, new_segment=True)
            )
        self.assertEqual(
            host.await_args.args,
            (
                "autoresearch.init",
                {
                    "name": "parser",
                    "metric": "time_ms",
                    "goal": None,
                    "unit": "",
                    "direction": "lower",
                    "secondary": [],
                    "scope": ["src"],
                    "off_limits": [],
                    "constraints": [],
                    "max_iterations": 4,
                    "new_segment": True,
                },
            ),
        )

    def test_log_formats_deltas_confidence_and_progress(self) -> None:
        module = _load("autoresearch_log")
        row = {"id": 2, "metric": "8", "metrics": [["size_kb", "3"]], "status": "keep"}
        reply = {
            "run": row,
            "flagged": [1],
            "deviations": [],
            "git": "committed abc",
            "stopped": False,
            "state": _state(),
        }
        host = AsyncMock(return_value=reply)
        with patch.object(module, "host_request", host):
            logged = asyncio.run(
                module.log("keep", "cache", flag_runs=[{"run": 1, "reason": "gamed"}])
            )
        self.assertEqual(
            host.await_args.args,
            (
                "autoresearch.log",
                {
                    "status": "keep",
                    "description": "cache",
                    "justification": None,
                    "flag_runs": [{"run": 1, "reason": "gamed"}],
                },
            ),
        )
        self.assertEqual(
            logged,
            {
                "run": {"id": 2, "metric": "8", "metrics": {"size_kb": "3"}, "status": "keep"},
                "vs_baseline": "-20.0%",
                "baseline": "10",
                "best": "8",
                "confidence": "2.5x noise floor (likely real)",
                "git": "committed abc",
                "deviations": [],
                "flagged": [1],
                "progress": "2/4",
                "stopped": False,
                "mode": "on",
            },
        )

    def test_arguments_are_checked_before_the_host(self) -> None:
        module = _load("autoresearch_checks")
        host = AsyncMock()
        with patch.object(module, "host_request", host):
            with self.assertRaisesRegex(ValueError, "status must be one of"):
                asyncio.run(module.log("better", "x"))
            with self.assertRaisesRegex(ValueError, "direction"):
                asyncio.run(module.init("n", "m", direction="up"))
            with self.assertRaisesRegex(TypeError, "not a string"):
                asyncio.run(module.init("n", "m", scope="src"))
            with self.assertRaisesRegex(TypeError, "flag_runs entry"):
                asyncio.run(module.log("discard", "x", flag_runs=[3]))
        host.assert_not_awaited()


if __name__ == "__main__":
    unittest.main()
