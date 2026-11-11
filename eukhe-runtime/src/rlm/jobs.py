"""The agent's own work, and the one blocking wait on it.

Work that outlives its call's blocking budget keeps running as a job: a
detached ``ipython`` cell or ``bash`` tool script. Besides those, the agent's
work is this kernel's ``bash()`` handles and its subagents.

``await jobs.wait()`` blocks until the first of that work settles and returns
it as a :class:`Job`; ``jobs.wait(target)`` waits on the named work only.
An input queued for this session meanwhile (a user steer, a peer's message,
a subagent's report, a job notice) ends the wait as a ``message`` job; the
message follows the cell's result. A result the wait returns is not
delivered again as a ``[job-settled]`` notice. The wait lasts ``timeout_s``
seconds, at most 30 minutes (the default), and returns ``None`` when nothing
settled in that time; with nothing to wait for it raises ``RuntimeError``.
A cell inside the wait does not detach at the blocking budget, and a cell
whose whole code is one ``await jobs.wait(...)`` with literal arguments runs
even while a detached cell holds the kernel.
"""

from __future__ import annotations

import asyncio
import uuid
from dataclasses import dataclass
from typing import Any

JOB_STATES = ("running", "ok", "error", "aborted", "killed")

_MESSAGE_TEXT = "A message arrived for this session; it follows this result."

# A wait asked for no length: the host caps it.
_UNBOUNDED_MS = 2**53

# A subagent's status (`rlm.collect`: queued, running, done, error,
# cancelled; the `rlm.list_subagents` roster: running, completed, error,
# cancelled) as a job state
_CHILD_STATES = {
    "queued": "running",
    "running": "running",
    "done": "ok",
    "completed": "ok",
    "error": "error",
    "cancelled": "aborted",
}


@dataclass(frozen=True)
class Job:
    """One piece of the agent's work: ``kind`` is ``cell`` or ``shell`` (a
    job of the session), ``bash`` (a ``bash()`` handle of this kernel),
    ``child`` (a subagent) or ``message`` (an input that ended a wait);
    ``state`` is ``running`` or how it settled (``ok``, ``error``,
    ``aborted``, ``killed``; a cancelled subagent is ``aborted``);
    ``output`` is the settled work's output (``None`` while it runs)."""

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


def _bash_job(handle: Any) -> Job:
    result = handle._result
    if result is None:
        return Job(id=f"bash-{handle._pid}", kind="bash", state="running", elapsed_ms=0)
    return Job(
        id=f"bash-{handle._pid}",
        kind="bash",
        state="ok" if result.exit_code == 0 else "error",
        elapsed_ms=int(result.duration * 1000),
        output=result.output,
    )


def _is_child(target: Any) -> bool:
    from . import RLMSpawnHandle, RLMSubagent

    return isinstance(target, (RLMSpawnHandle, RLMSubagent))


def _waitable_handles() -> list[Any]:
    """This kernel's ``bash()`` handles whose result has not reached the model:
    running, or settled with no read and no admitted notice."""
    from .bash import _activity_handles, _live_lock

    with _live_lock:
        handles = list(_activity_handles.values())
    return [
        h
        for h in handles
        if not h._result_consumed and not h._awaited_by_creating_cell and not h._noticed
    ]


def _send_wait_event(data: dict[str, Any]) -> None:
    """Tell the host about the wait in flight, fire-and-forget: the reply is
    never needed (unknown reply ids are dropped)."""
    from . import repl

    if not repl.is_active():
        return
    repl._send(
        {
            "event": "host_request",
            "id": uuid.uuid4().hex,
            "data": {**data, "type": "jobs.wait_event"},
        }
    )


def _timeout_s(timeout_s: Any) -> int | None:
    if timeout_s is None:
        return None
    if isinstance(timeout_s, bool) or not isinstance(timeout_s, (int, float)) or timeout_s < 0:
        raise TypeError("timeout_s must be a non-negative number of seconds")
    whole = int(timeout_s)
    return whole if whole == timeout_s else whole + 1


class _JobsNamespace:
    async def list(self) -> list[Job]:
        """The agent's work: the session's jobs (running ones and the latest
        settled ones), this kernel's ``bash()`` handles and the subagents."""
        from . import host_request, list_subagents
        from .bash import _activity_handles, _live_lock

        payload = await host_request("jobs.list")
        entries = payload.get("jobs")
        if not isinstance(entries, list):
            raise RuntimeError("jobs.list returned an invalid jobs list")
        found = [_job_from_payload(entry, "jobs.list") for entry in entries]
        with _live_lock:
            handles = list(_activity_handles.values())
        found.extend(_bash_job(handle) for handle in handles)
        for child in await list_subagents():
            found.append(
                Job(
                    id=child.rlm_child_id,
                    kind="child",
                    state=_CHILD_STATES[child.status],
                    elapsed_ms=child.duration_ms or 0,
                    output=child.answer_preview,
                )
            )
        return found

    async def wait(self, targets: Any = None, *, timeout_s: float | None = None) -> Job | None:
        """Block until the first of the agent's work settles and return it.

        ``targets`` is ``None`` (all of the agent's work), or a job id, a
        :class:`Job`, a ``bash()`` handle, a subagent (spawn handle or row),
        or a list of them; subagents are waited on alone, like
        ``rlm.collect``. An input queued for this session ends the wait as a
        ``message`` job. ``timeout_s`` (default and cap: 1800) bounds the
        wait; ``None`` when nothing settled in time. Raises ``RuntimeError``
        when nothing is running or ready."""
        from .bash import BashHandle

        seconds = _timeout_s(timeout_s)
        items: list[Any] | None
        if targets is None:
            items = None
        elif isinstance(targets, (list, tuple)):
            items = list(targets)
            if not items:
                raise ValueError("targets must not be empty; pass None to wait on all work")
        else:
            items = [targets]
        if items is not None and any(_is_child(item) for item in items):
            if not all(_is_child(item) for item in items):
                raise TypeError(
                    "wait on subagents alone (or call jobs.wait() for whatever settles first)"
                )
            return await _wait_children(items, seconds)
        if items is None:
            return await _wait(_waitable_handles(), None, seconds)
        local = [item for item in items if isinstance(item, BashHandle)]
        named = [_job_id(item) for item in items if not isinstance(item, BashHandle)]
        return await _wait(local, named, seconds)

    async def cancel(self, target: Any) -> Job:
        """Stop one piece of work: a session job (a cell is interrupted, and
        its kernel killed when the interrupt is not honored within the
        grace), a ``bash()`` handle (killed) or a subagent (deleted).
        Returns it once it settled, or as it is when the budget ran out."""
        from . import delete_subagent, host_request
        from .bash import BashHandle

        if isinstance(target, BashHandle):
            target.kill()
            return _bash_job(target)
        if _is_child(target):
            row = await delete_subagent(target)
            return Job(id=row.rlm_child_id, kind="child", state="aborted", elapsed_ms=row.duration_ms or 0)
        payload = await host_request("jobs.cancel", {"job": _job_id(target)})
        return _job_from_payload(payload, "jobs.cancel")


def _job_id(job: Any) -> str:
    if isinstance(job, Job):
        return job.id
    if isinstance(job, str) and job:
        return job
    raise TypeError("a target must be a job id string, a Job, a bash() handle or a subagent")


async def _wait(local: list[Any], named: list[str] | None, seconds: int | None) -> Job | None:
    from . import host_request

    wait_id = uuid.uuid4().hex
    # targets: None waits on all work; a list (empty: only the handles)
    # names the session jobs.
    payload: dict[str, Any] = {
        "targets": named,
        "local": ["ready" if handle._done.is_set() else "running" for handle in local],
        "timeout_s": seconds,
        "wait_id": wait_id,
    }
    host = asyncio.ensure_future(host_request("jobs.wait", payload))
    watchers = {
        asyncio.ensure_future(handle._wait()): index
        for index, handle in enumerate(local)
        if not handle._done.is_set()
    }
    try:
        while True:
            done, _ = await asyncio.wait({host, *watchers}, return_when=asyncio.FIRST_COMPLETED)
            for finished in done - {host}:
                _send_wait_event({"wait_id": wait_id, "local": watchers.pop(finished)})
            if host in done:
                break
    except asyncio.CancelledError:
        _send_wait_event({"wait_id": wait_id, "cancel": True})
        host.cancel()
        raise
    finally:
        for watcher in watchers:
            watcher.cancel()
    reply = host.result()
    end = reply.get("end")
    if end == "job":
        return _job_from_payload(reply.get("job"), "jobs.wait")
    if end == "local":
        handle = local[reply["index"]]
        handle._note_result_consumed()
        return _bash_job(handle)
    if end == "message":
        return Job(id="message", kind="message", state="ok", elapsed_ms=0, output=_MESSAGE_TEXT)
    if end in ("timeout", "cancelled"):
        return None
    raise RuntimeError("jobs.wait returned an invalid end")


async def _wait_children(children: list[Any], seconds: int | None) -> Job | None:
    from . import collect

    # The host caps the wait at its 30 minutes.
    timeout_ms = _UNBOUNDED_MS if seconds is None else seconds * 1000
    results = await collect(children, timeout_ms=timeout_ms)
    for result in results:
        if result.settled:
            return Job(
                id=result.rlm_child_id,
                kind="child",
                state=_CHILD_STATES[result.status],
                elapsed_ms=result.duration_ms or 0,
                output=result.answer_preview if result.error is None else result.error,
            )
    return None


jobs = _JobsNamespace()
