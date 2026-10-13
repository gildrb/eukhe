"""The session's jobs: work that outlived its call's blocking budget.

A cell still running when the runtime's blocking budget expires keeps
running as a job; its call returns the output so far, and the job's end
reaches the session as a ``[job-settled job:ID status:S]`` message. This
module lists, waits on, and cancels those jobs through the host. Every wait
is clamped by the host to the same budget, so no call here holds a cell
past it. A cancel interrupts the job's cell and kills its kernel when the
interrupt is not honored within the grace.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

JOB_STATES = ("running", "ok", "error", "aborted", "killed")


@dataclass(frozen=True)
class Job:
    """One job: ``state`` is ``running`` or how it settled; ``output`` is the
    settled job's bounded output (``None`` while it runs)."""

    id: str
    kind: str
    state: str
    elapsed_ms: int
    output: str | None = None

    @property
    def settled(self) -> bool:
        return self.state != "running"


def _job_from_payload(payload: Any, request_type: str) -> Job:
    if not isinstance(payload, dict):
        raise RuntimeError(f"{request_type} returned an invalid job")
    job_id = payload.get("id")
    kind = payload.get("kind")
    state = payload.get("state")
    elapsed_ms = payload.get("elapsed_ms")
    output = payload.get("output")
    if (
        not isinstance(job_id, str)
        or not job_id
        or not isinstance(kind, str)
        or state not in JOB_STATES
        or not isinstance(elapsed_ms, int)
        or isinstance(elapsed_ms, bool)
        or not (output is None or isinstance(output, str))
    ):
        raise RuntimeError(f"{request_type} returned an invalid job")
    return Job(id=job_id, kind=kind, state=state, elapsed_ms=elapsed_ms, output=output)


def _job_id(job: str | Job) -> str:
    if isinstance(job, Job):
        return job.id
    if isinstance(job, str) and job:
        return job
    raise TypeError("job must be a job id string or a Job")


class _JobsNamespace:
    async def list(self) -> list[Job]:
        """Every job of this session, running ones and the latest settled ones."""
        from . import host_request

        payload = await host_request("jobs.list")
        entries = payload.get("jobs")
        if not isinstance(entries, list):
            raise RuntimeError("jobs.list returned an invalid jobs list")
        return [_job_from_payload(entry, "jobs.list") for entry in entries]

    async def wait(self, job: str | Job, *, timeout_ms: int | None = None) -> Job:
        """Wait for ``job`` to settle; ``timeout_ms`` (default: the blocking
        budget) is clamped to the budget. Returns the job as it is when the
        wait ends: still ``running`` when it did not settle in time."""
        from . import host_request

        payload: dict[str, Any] = {"job": _job_id(job)}
        if timeout_ms is not None:
            if not isinstance(timeout_ms, int) or isinstance(timeout_ms, bool) or timeout_ms < 0:
                raise TypeError("timeout_ms must be a non-negative int")
            payload["timeout_ms"] = timeout_ms
        return _job_from_payload(await host_request("jobs.wait", payload), "jobs.wait")

    async def cancel(self, job: str | Job) -> Job:
        """Stop ``job``: its cell is interrupted, and its kernel killed when the
        interrupt is not honored within the grace (effects then unknown).
        Returns the job once it settled, or as it is when the budget ran out."""
        from . import host_request

        payload = await host_request("jobs.cancel", {"job": _job_id(job)})
        return _job_from_payload(payload, "jobs.cancel")


jobs = _JobsNamespace()
