from __future__ import annotations

import asyncio
import importlib
import unittest
from unittest.mock import AsyncMock, patch

rlm_module = importlib.import_module("rlm")


class RlmQueryTest(unittest.TestCase):
    def test_query_returns_the_answer_as_a_str_value(self) -> None:
        host_request = AsyncMock(
            return_value={"results": [{"text": "a summary", "truncated": False, "model": "faux/faux-1"}]}
        )
        with patch.object(rlm_module, "host_request", host_request):
            answer = asyncio.run(rlm_module.rlm.query("summarize", "the long context", max_bytes=64))

        self.assertEqual((answer, answer.truncated, answer.model), ("a summary", False, "faux/faux-1"))
        self.assertIsInstance(answer, str)
        host_request.assert_awaited_once_with(
            "rlm.query_batch",
            {"calls": [{"prompt": "summarize", "context": 0, "max_bytes": 64}], "contexts": ["the long context"]},
        )

    def test_a_batch_sends_a_shared_context_once_and_keeps_failures_in_place(self) -> None:
        host_request = AsyncMock(
            return_value={
                "results": [
                    {"text": "one", "truncated": True, "model": "p/a"},
                    {"error": "the provider failed"},
                    {"text": "three", "truncated": False, "model": "p/b"},
                ]
            }
        )
        with patch.object(rlm_module, "host_request", host_request):
            results = asyncio.run(
                rlm_module.rlm.query_batch(
                    [
                        {"prompt": "a", "context": "shared"},
                        {"prompt": "b", "context": "shared", "model": "p/a", "thinking": "low"},
                        {"prompt": "c", "context": None},
                    ],
                    concurrency=2,
                )
            )

        self.assertEqual([str(result) for result in results], ["one", "the provider failed", "three"])
        self.assertIsInstance(results[1], rlm_module.RLMQueryError)
        self.assertTrue(results[0].truncated)
        host_request.assert_awaited_once_with(
            "rlm.query_batch",
            {
                "calls": [
                    {"prompt": "a", "context": 0},
                    {"prompt": "b", "context": 0, "model": "p/a", "thinking": "low"},
                    {"prompt": "c"},
                ],
                "contexts": ["shared"],
                "concurrency": 2,
            },
        )

    def test_a_refused_batch_raises_its_refusal_text(self) -> None:
        refusal = "rlm.query concurrency limit 4 is already full"
        host_request = AsyncMock(return_value={"refused": refusal})
        with patch.object(rlm_module, "host_request", host_request):
            with self.assertRaisesRegex(rlm_module.RLMQueryError, "^rlm.query concurrency limit 4 is already full$"):
                asyncio.run(rlm_module.rlm.query_batch([{"prompt": "a"}]))

    def test_a_failed_query_raises(self) -> None:
        host_request = AsyncMock(return_value={"results": [{"error": "no model"}]})
        with patch.object(rlm_module, "host_request", host_request):
            with self.assertRaisesRegex(rlm_module.RLMQueryError, "^no model$"):
                asyncio.run(rlm_module.query("a"))

    def test_bad_calls_fail_before_any_request(self) -> None:
        host_request = AsyncMock()
        cases = [
            ([], {}, "calls must be a non-empty list"),
            ([{"prompt": "a", "tools": []}], {}, "unsupported keys: tools"),
            ([{"prompt": 1}], {}, "prompt must be str"),
            ([{"prompt": "a", "max_bytes": 0}], {}, "max_bytes must be a positive int"),
            ([{"prompt": "a", "max_bytes": True}], {}, "max_bytes must be a positive int"),
            ([{"prompt": "a"}], {"concurrency": 0}, "concurrency must be a positive int"),
        ]
        with patch.object(rlm_module, "host_request", host_request):
            for calls, kwargs, message in cases:
                with self.subTest(message=message):
                    with self.assertRaisesRegex(TypeError, message):
                        asyncio.run(rlm_module.rlm.query_batch(calls, **kwargs))
        host_request.assert_not_awaited()


if __name__ == "__main__":
    unittest.main()
