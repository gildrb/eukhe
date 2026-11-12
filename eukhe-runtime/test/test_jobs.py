from __future__ import annotations

import asyncio
import importlib
import unittest
from pathlib import Path
from typing import Any
from unittest.mock import AsyncMock, patch


rlm_module = importlib.import_module("rlm")
bash_module = importlib.import_module("rlm.bash")


def _settled(job_id: str = "shell-1") -> dict[str, object]:
    return {"id": job_id, "kind": "shell", "state": "ok", "elapsed_ms": 45_000, "output": "BUILD-OK\n"}


def _host(replies: dict[str, Any]) -> AsyncMock:
    """A host that answers each request type with its reply."""

    async def answer(request_type: str, payload: dict[str, Any] | None = None) -> Any:
        return replies[request_type]

    return AsyncMock(side_effect=answer)


class JobsApiTest(unittest.TestCase):
    def setUp(self) -> None:
        # This kernel's bash() handles of other tests are no work of these.
        handles = patch.dict(bash_module._activity_handles, clear=True)
        handles.start()
        self.addCleanup(handles.stop)

    def test_lists_the_session_jobs_and_the_subagents(self) -> None:
        running = {"id": "cell-1", "kind": "cell", "state": "running", "elapsed_ms": 1200}
        child = {
            "rlm_child_id": "child-1",
            "session_name": "worker",
            "session_dir": "/tmp/worker",
            "status": "running",
        }
        host_request = _host({"jobs.list": {"jobs": [_settled(), running]}, "rlm.list_subagents": {"subagents": [child]}})

        with patch.object(rlm_module, "host_request", host_request):
            listed = asyncio.run(rlm_module.jobs.list())

        self.assertEqual(
            [(job.id, job.kind, job.state) for job in listed],
            [("shell-1", "shell", "ok"), ("cell-1", "cell", "running"), ("child-1", "child", "running")],
        )
        self.assertEqual(listed[0].output, "BUILD-OK\n")
        self.assertIsNone(listed[1].output)

    def test_lists_a_cancelled_subagent_as_an_aborted_job(self) -> None:
        # The roster row of a child whose run was cancelled (Esc on the cell
        # that waited on it) reads `cancelled`.
        child = {
            "rlm_child_id": "child-1",
            "session_name": "worker",
            "session_dir": "/tmp/worker",
            "status": "cancelled",
            "duration_ms": 2400,
        }
        host_request = _host({"jobs.list": {"jobs": []}, "rlm.list_subagents": {"subagents": [child]}})

        with patch.object(rlm_module, "host_request", host_request):
            listed = asyncio.run(rlm_module.jobs.list())

        self.assertEqual(listed, [rlm_module.Job("child-1", "child", "aborted", 2400)])
        self.assertTrue(listed[0].settled)

    def test_cancel_of_a_running_subagent_returns_it_aborted(self) -> None:
        # jobs.cancel deletes the child; the deleted row of a child that
        # was running reads `cancelled`.
        deleted = {
            "rlm_child_id": "child-1",
            "session_name": "worker",
            "session_dir": "/tmp/worker",
            "status": "cancelled",
            "duration_ms": 2400,
        }
        host_request = _host({"rlm.delete_subagent": {"subagent": deleted, "outcome": "deleted"}})
        handle = rlm_module.RLMSpawnHandle(
            rlm_child_id="child-1", name="worker", session_dir=Path("/tmp/worker"), model="stub/stub-1"
        )

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.cancel(handle))

        host_request.assert_awaited_once_with("rlm.delete_subagent", {"target": "child-1"})
        self.assertEqual(job, rlm_module.Job("child-1", "child", "aborted", 2400))

    def test_wait_on_all_work_returns_the_first_settled_job(self) -> None:
        host_request = _host({"jobs.wait": {"end": "job", "job": _settled()}})

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.wait())

        request_type, payload = host_request.await_args.args
        self.assertEqual(request_type, "jobs.wait")
        self.assertEqual(
            {key: value for key, value in payload.items() if key != "wait_id"},
            {"targets": None, "local": [], "timeout_s": None},
        )
        self.assertEqual(job, rlm_module.Job("shell-1", "shell", "ok", 45_000, "BUILD-OK\n"))

    def test_wait_names_its_targets_and_rounds_the_timeout_up(self) -> None:
        host_request = _host({"jobs.wait": {"end": "timeout"}})

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(
                rlm_module.jobs.wait(["cell-1", rlm_module.Job("shell-2", "shell", "running", 0)], timeout_s=1.5)
            )

        payload = host_request.await_args.args[1]
        self.assertEqual((payload["targets"], payload["timeout_s"]), (["cell-1", "shell-2"], 2))
        self.assertIsNone(job)

    def test_a_queued_message_ends_the_wait(self) -> None:
        host_request = _host({"jobs.wait": {"end": "message"}})

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.wait())

        self.assertEqual((job.kind, job.output), ("message", "A message arrived for this session; it follows this result."))

    def test_cancel_returns_the_settled_job(self) -> None:
        killed = {"id": "cell-1", "kind": "cell", "state": "killed", "elapsed_ms": 3000, "output": ""}
        host_request = _host({"jobs.cancel": killed})

        with patch.object(rlm_module, "host_request", host_request):
            job = asyncio.run(rlm_module.jobs.cancel("cell-1"))

        host_request.assert_awaited_once_with("jobs.cancel", {"job": "cell-1"})
        self.assertEqual(job.state, "killed")

    def test_rejects_bad_arguments_and_bad_replies(self) -> None:
        host_request = _host({"jobs.wait": {"end": "lost"}})
        with patch.object(rlm_module, "host_request", host_request):
            with self.assertRaises(TypeError):
                asyncio.run(rlm_module.jobs.wait("cell-1", timeout_s=-1))
            with self.assertRaises(ValueError):
                asyncio.run(rlm_module.jobs.wait([]))
            with self.assertRaises(TypeError):
                asyncio.run(rlm_module.jobs.cancel(""))
            with self.assertRaises(RuntimeError):
                asyncio.run(rlm_module.jobs.wait("cell-1"))


if __name__ == "__main__":
    unittest.main()
