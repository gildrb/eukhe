from __future__ import annotations

import asyncio
import importlib
import unittest
from unittest.mock import AsyncMock, patch


rlm_module = importlib.import_module("rlm")


def _running(job_id: str = "cell-1") -> dict[str, object]:
    return {"id": job_id, "kind": "cell", "state": "running", "elapsed_ms": 1200}


class JobsApiTest(unittest.TestCase):
    def test_lists_the_session_jobs(self) -> None:
        settled = {"id": "cell-0", "kind": "cell", "state": "ok", "elapsed_ms": 90, "output": "42"}
        host_request = AsyncMock(return_value={"jobs": [settled, _running()]})

        with patch.object(rlm_module, "host_request", host_request):
            listed = asyncio.run(rlm_module.jobs.list())

        host_request.assert_awaited_once_with("jobs.list")
        self.assertEqual([job.id for job in listed], ["cell-0", "cell-1"])
        self.assertTrue(listed[0].settled)
        self.assertEqual(listed[0].output, "42")
        self.assertFalse(listed[1].settled)
        self.assertIsNone(listed[1].output)

    def test_wait_forwards_the_timeout_and_reports_a_job_still_running(self) -> None:
        host_request = AsyncMock(return_value=_running())

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.wait("cell-1", timeout_ms=500))

        host_request.assert_awaited_once_with("jobs.wait", {"job": "cell-1", "timeout_ms": 500})
        self.assertEqual(job.state, "running")

    def test_wait_without_a_timeout_leaves_the_bound_to_the_host_budget(self) -> None:
        host_request = AsyncMock(return_value=_running())

        with patch.object(rlm_module, "host_request", host_request):
            asyncio.run(rlm_module.jobs.wait(rlm_module.Job("cell-1", "cell", "running", 0)))

        host_request.assert_awaited_once_with("jobs.wait", {"job": "cell-1"})

    def test_cancel_returns_the_settled_job(self) -> None:
        killed = {"id": "cell-1", "kind": "cell", "state": "killed", "elapsed_ms": 3000, "output": ""}
        host_request = AsyncMock(return_value=killed)

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.cancel("cell-1"))

        host_request.assert_awaited_once_with("jobs.cancel", {"job": "cell-1"})
        self.assertEqual(job.state, "killed")

    def test_rejects_bad_arguments_and_bad_replies(self) -> None:
        host_request = AsyncMock(return_value={"id": "cell-1", "state": "lost"})
        with patch.object(rlm_module, "host_request", host_request):
            with self.assertRaises(TypeError):
                asyncio.run(rlm_module.jobs.wait("cell-1", timeout_ms=-1))
            with self.assertRaises(TypeError):
                asyncio.run(rlm_module.jobs.cancel(""))
            with self.assertRaises(RuntimeError):
                asyncio.run(rlm_module.jobs.wait("cell-1"))


if __name__ == "__main__":
    unittest.main()
