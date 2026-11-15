"""Tiny rlm-compatible kernel shim for Eukhe."""

from __future__ import annotations

import sys
import types
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .bash import BashHandle, BashResult, bash
from .factory import (
    FACTORY_HELP,
    graph_factory,
    resume_factory,
    run_factory,
    status_factory,
    stop_factory,
    watch_factory,
)
from .harness import (
    CHAT_MEMORY_ABSENT_METHODS,
    CHAT_MEMORY_MESSAGE,
    HarnessEntry,
    HarnessScope,
    HarnessState,
    RefinementEvent,
    chat_memory_session,
    get_harness_state,
)
from .history import ChatLine, HistoryEntry, ToolCall, chat, history
from .jobs import Job, jobs
from .query import RLMQueryError, RLMText, query, query_batch
from .remote import remote

_NOT_CALLABLE_MESSAGE = "'rlm' is not callable; split work with: left, right = await rlm.split(left={'scope': ['src/a'], 'task': '...'}, right={'scope': ['src/b'], 'task': '...'}), or ask a read-only helper with: handle = await rlm.spawn('question', name='helper')"
_RENAMED_RUN_MESSAGE = "rlm.run was renamed; ask a read-only helper with: handle = await rlm.spawn('question', name='helper')"


@dataclass(frozen=True)
class RLMSpawnHandle:
    rlm_child_id: str
    name: str
    session_dir: Path
    model: str


@dataclass(frozen=True)
class RLMModel:
    provider: str
    id: str
    name: str
    selector: str


@dataclass(frozen=True)
class RLMSubagentActivity:
    kind: str
    tool_name: str | None = None


# The run status of a roster row: `cancelled` is a child whose run was
# stopped before it answered (Esc on the cell that waited on it, a cancel,
# a delete of the running child); the row stays until the child is deleted.
SUBAGENT_STATUSES = ("running", "completed", "error", "cancelled")


@dataclass(frozen=True)
class RLMSubagent:
    """One direct child as ``list_subagents()`` rows it: ``status`` is
    ``running``, ``completed``, ``error`` or ``cancelled`` (its run was
    stopped before it answered)."""

    rlm_child_id: str
    active_session_id: str | None
    session_id: str | None
    session_name: str
    session_dir: Path
    status: str
    activity: RLMSubagentActivity | None = None
    tool_use_count: int | None = None
    duration_ms: int | None = None
    answer_preview: str | None = None
    replied_since_task: bool | None = None
    progress_note: str | None = None
    label: str | None = None
    last_activity_at: float | None = None
    activity_stale_ms: float | None = None
    handback: str | None = None


@dataclass(frozen=True)
class RLMProgressNoteResult:
    accepted: bool
    retry_after_ms: int | None = None


@dataclass(frozen=True)
class RLMChildResult:
    """Terminal or in-progress state of one direct child, from `collect()`."""

    rlm_child_id: str
    session_name: str | None
    session_dir: Path | None
    status: str
    settled: bool
    answer_preview: str | None
    error: str | None
    duration_ms: int | None
    tool_use_count: int | None
    replied_since_task: bool | None
    handback: str | None = None
    acceptance: str | None = None


def _spawn_handle_from_payload(payload: Any) -> RLMSpawnHandle:
    if not isinstance(payload, dict):
        raise RuntimeError("rlm.spawn returned an invalid spawn handle")
    child_id = payload.get("rlm_child_id")
    name = payload.get("name")
    session_dir = payload.get("session_dir")
    model = payload.get("model")
    if not all(isinstance(value, str) and value for value in (child_id, name, session_dir, model)):
        raise RuntimeError("rlm.spawn returned an invalid spawn handle")
    return RLMSpawnHandle(
        rlm_child_id=child_id,
        name=name,
        session_dir=Path(session_dir),
        model=model,
    )


def _parse_host_reply(request_type: str, reply: dict[str, Any]) -> dict[str, Any]:
    status = reply.get("status")
    if status == "ok":
        return reply["result"]
    if status == "error":
        raise RuntimeError(str(reply.get("error") or f"host request {request_type} failed"))
    raise RuntimeError(f"host request {request_type} returned unexpected status: {status!r}")


async def host_request(request_type: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    """Send a typed request to the Eukhe host and await its reply.

    This is the kernel side of the generic host bridge: Python skills call
    ``await host_request("<type>", {...})`` and the TypeScript host dispatches
    on the type. Raises RuntimeError when the host reports an error or when no
    handler for the type is registered in this session.
    """
    if not isinstance(request_type, str) or not request_type:
        raise TypeError("request_type must be a non-empty str")
    if payload is not None and not isinstance(payload, dict):
        raise TypeError(f"payload must be a dict or None, got {type(payload).__name__}")
    from . import repl

    # request_type goes last so a payload "type" key cannot reroute the request.
    reply = await repl.host_request({**(payload or {}), "type": request_type})
    return _parse_host_reply(request_type, reply)


def host_request_sync(request_type: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    """Like :func:`host_request`, but blocks instead of awaiting.

    For short host work behind synchronous kernel functions (``read``,
    ``edit``, ...). Raises RuntimeError like :func:`host_request`.
    """
    if not isinstance(request_type, str) or not request_type:
        raise TypeError("request_type must be a non-empty str")
    if payload is not None and not isinstance(payload, dict):
        raise TypeError(f"payload must be a dict or None, got {type(payload).__name__}")
    from . import repl

    reply = repl.host_request_sync({**(payload or {}), "type": request_type})
    return _parse_host_reply(request_type, reply)


def emit(data: dict[str, Any]) -> None:
    """Ship one display event (dict of MIME type -> JSON payload) to the host."""
    from . import repl

    repl.emit(data)


async def spawn(
    prompt: str,
    *,
    name: str,
    model: str | None = None,
    thinking: str | None = None,
    budget: dict[str, Any] | None = None,
    accept: list[dict[str, Any]] | None = None,
    accept_intent: bool | None = None,
    accept_returns: int | None = None,
) -> RLMSpawnHandle:
    """Ask a read-only help leaf and return once its task is admitted.

    A help leaf reads, searches and answers; it writes nothing (its tools are
    read-only, in this agent's workspace). It counts as one node of this
    agent's tree, takes its limit from this agent's free budget, is cancelled
    with this agent's subtree, and its result arrives like a child's report.
    To have work written by other agents, use :func:`split`.
    ``name`` is required and must be unique among siblings.
    ``model`` selects a child with an exact ``provider/model`` selector.
    ``thinking`` sets the child reasoning level (e.g. 'off', 'low', 'medium', 'high');
    defaults to the parent level; levels invalid for the resolved model fail the spawn.
    ``budget``: the leaf's limit, a dict with any of ``cost_usd``, ``tokens``,
    ``time_s``, ``tool_calls``, ``requests``; default: a tenth of what this agent
    may still spend. A leaf the tree has no room or budget for is refused.
    ``accept``: the child's acceptance checks, this agent their owner (only
    this agent sets them): a list of ``{"kind": "command", "command": "pytest -q",
    "expect": 0, "timeout_ms"?: int, "protect"?: [paths]}``,
    ``{"kind": "judge", "condition": str, "evidence"?: [commands], "model"?: str}``
    or ``{"kind": "until", "command": str, "timeout_ms"?: int}``. The child's
    "done" counts only when the harness confirms every check on its final state;
    its report and ``collect()`` carry the verdict (``checks passed, unconfined``,
    ``failed`` or ``unverified``). ``accept_intent`` (default True with ``accept``)
    adds the intent check: a judge (one model request with no tools and no
    transcript) decides from the child's task whether its
    final state meets it. ``accept_returns``: the most times in a row a refuted
    "done" goes back to the child before it ends failed.
    """
    if not isinstance(prompt, str):
        raise TypeError(f"prompt must be str, got {type(prompt).__name__}")
    kwargs: dict[str, Any] = {"name": name}
    if model is not None:
        kwargs["model"] = model
    if thinking is not None:
        kwargs["thinking"] = thinking
    if budget is not None:
        kwargs["budget"] = budget
    if accept is not None:
        kwargs["accept"] = accept
    if accept_intent is not None:
        kwargs["accept_intent"] = accept_intent
    if accept_returns is not None:
        kwargs["accept_returns"] = accept_returns
    payload = await host_request("rlm.run", {"prompt": prompt, "kwargs": kwargs})
    return _spawn_handle_from_payload(payload)


_SPLIT_HALF_KEYS = (
    "scope",
    "task",
    "name",
    "model",
    "thinking",
    "accept",
    "accept_intent",
    "accept_returns",
)


def _split_half(half: Any, side: str) -> dict[str, Any]:
    if not isinstance(half, dict):
        raise TypeError(f"{side} must be a dict {{'scope': [paths], 'task': str}}")
    unknown = sorted(set(half) - set(_SPLIT_HALF_KEYS))
    if unknown:
        raise TypeError(f"unsupported {side} keys: {', '.join(unknown)}")
    scope = half.get("scope")
    if not isinstance(scope, list) or not scope or not all(isinstance(path, str) for path in scope):
        raise TypeError(f"{side} scope must be a non-empty list of path strings")
    if not isinstance(half.get("task"), str):
        raise TypeError(f"{side} task must be str")
    return {key: value for key, value in half.items() if value is not None}


async def split(
    left: dict[str, Any],
    right: dict[str, Any],
    own: list[str] | None = None,
    hold: int | None = None,
) -> tuple[RLMSpawnHandle, RLMSpawnHandle]:
    """Split this agent's work into two children; return their handles.

    Split when the work has two halves that write disjoint files and each is
    worth its own planning (several edits or files); otherwise do it yourself.
    Never split sequential work (one half needs the other's result).

    ``left`` and ``right``: ``{"scope": [paths], "task": str, "name"?: str,
    "model"?: str, "thinking"?: str, "accept"?: list[dict], "accept_intent"?: bool,
    "accept_returns"?: int}``. A scope names files or directories relative to
    the workspace root; a child writes only there, in its own copy of this
    agent's workspace (uncommitted edits included). When a child finishes, its
    writes inside its scope are applied to this agent's workspace; its writes
    outside return as conflicts, never applied. A failed child runs again once
    from its partial work; a child that fails again reports its failure and its
    partial work stays in its own copy.
    ``own``: the paths this agent keeps writing; default: the rest of its scope.
    Keep shared files (lockfiles, mod.rs, index files, generated code) in ``own``.
    ``own``, ``left`` and ``right`` must split this agent's scope exactly, each
    half non-empty. ``hold``: budget this agent keeps for itself; default: two
    worst-case requests or a tenth of what it may spend, whichever is more. Each
    child gets half of the rest; what a child leaves unspent returns when it settles.
    The tree is at most 3 levels deep and 15 agents in all. A refused split names
    its first failing check and starts nothing.

    While children run, work on ``own``; integrate each result as it arrives
    (its report comes as a message), run the check, report.
    """
    payload: dict[str, Any] = {
        "left": _split_half(left, "left"),
        "right": _split_half(right, "right"),
    }
    if own is not None:
        if not isinstance(own, list) or not all(isinstance(path, str) for path in own):
            raise TypeError("own must be a list of path strings or None")
        payload["own"] = own
    if hold is not None:
        if not isinstance(hold, int) or hold < 0:
            raise TypeError("hold must be a non-negative int or None")
        payload["hold"] = hold
    reply = await host_request("rlm.split", payload)
    return (
        _spawn_handle_from_payload(reply.get("left")),
        _spawn_handle_from_payload(reply.get("right")),
    )


def _model_from_payload(payload: Any) -> RLMModel:
    if not isinstance(payload, dict):
        raise RuntimeError("rlm.find_models returned an invalid model entry")
    provider = payload.get("provider")
    model_id = payload.get("id")
    name = payload.get("name")
    selector = payload.get("selector")
    if not all(isinstance(value, str) and value for value in (provider, model_id, name, selector)):
        raise RuntimeError("rlm.find_models returned an invalid model entry")
    return RLMModel(provider=provider, id=model_id, name=name, selector=selector)


async def find_models(query: str = "", limit: int = 8) -> list[RLMModel]:
    """Search a bounded list of models backed by active user credentials."""
    if not isinstance(query, str):
        raise TypeError(f"query must be str, got {type(query).__name__}")
    if not isinstance(limit, int):
        raise TypeError(f"limit must be int, got {type(limit).__name__}")
    payload = await host_request("rlm.find_models", {"query": query, "limit": limit})
    models = payload.get("models")
    if not isinstance(models, list):
        raise RuntimeError("rlm.find_models returned an invalid models list")
    return [_model_from_payload(model) for model in models]


def _optional_str_field(payload: dict[str, Any], field: str, operation: str) -> str | None:
    value = payload.get(field)
    if value is None:
        return None
    if not isinstance(value, str):
        raise RuntimeError(f"{operation} entry has invalid {field}")
    return value


def _optional_int_field(payload: dict[str, Any], field: str, operation: str) -> int | None:
    value = payload.get(field)
    if value is None:
        return None
    if not isinstance(value, int) or isinstance(value, bool):
        raise RuntimeError(f"{operation} entry has invalid {field}")
    return value


def _optional_bool_field(payload: dict[str, Any], field: str, operation: str) -> bool | None:
    value = payload.get(field)
    if value is None:
        return None
    if not isinstance(value, bool):
        raise RuntimeError(f"{operation} entry has invalid {field}")
    return value


def _optional_activity_field(payload: dict[str, Any], operation: str) -> RLMSubagentActivity | None:
    value = payload.get("activity")
    if value is None:
        return None
    if not isinstance(value, dict):
        raise RuntimeError(f"{operation} entry has invalid activity")
    kind = value.get("kind")
    if kind not in {"waiting", "writing", "executing"}:
        raise RuntimeError(f"{operation} entry has invalid activity kind")
    tool_name = value.get("tool_name")
    if tool_name is not None and not isinstance(tool_name, str):
        raise RuntimeError(f"{operation} entry has invalid activity tool_name")
    return RLMSubagentActivity(kind=kind, tool_name=tool_name)


def _subagent_from_payload(payload: Any, operation: str = "rlm.list_subagents") -> RLMSubagent:
    if not isinstance(payload, dict):
        raise RuntimeError(f"{operation} returned an invalid subagent entry")
    child_id = payload.get("rlm_child_id")
    active_session_id = payload.get("active_session_id")
    session_id = payload.get("session_id")
    session_name = payload.get("session_name")
    session_dir = payload.get("session_dir")
    status = payload.get("status")
    if not isinstance(child_id, str) or not child_id:
        raise RuntimeError(f"{operation} entry is missing rlm_child_id")
    if active_session_id is not None and not isinstance(active_session_id, str):
        raise RuntimeError(f"{operation} entry has invalid active_session_id")
    if session_id is not None and not isinstance(session_id, str):
        raise RuntimeError(f"{operation} entry has invalid session_id")
    if not isinstance(session_name, str) or not session_name:
        raise RuntimeError(f"{operation} entry is missing session_name")
    if not isinstance(session_dir, str) or not session_dir:
        raise RuntimeError(f"{operation} entry is missing session_dir")
    if status not in SUBAGENT_STATUSES:
        raise RuntimeError(f"{operation} entry has invalid status")
    return RLMSubagent(
        rlm_child_id=child_id,
        active_session_id=active_session_id,
        session_id=session_id,
        session_name=session_name,
        session_dir=Path(session_dir),
        status=status,
        activity=_optional_activity_field(payload, operation),
        tool_use_count=_optional_int_field(payload, "tool_use_count", operation),
        duration_ms=_optional_int_field(payload, "duration_ms", operation),
        answer_preview=_optional_str_field(payload, "answer_preview", operation),
        replied_since_task=_optional_bool_field(payload, "replied_since_task", operation),
        progress_note=_optional_str_field(payload, "progress_note", operation),
        label=_optional_str_field(payload, "label", operation),
        last_activity_at=_optional_int_field(payload, "last_activity_at", operation),
        activity_stale_ms=_optional_int_field(payload, "activity_stale_ms", operation),
        handback=_optional_str_field(payload, "handback", operation),
    )


async def list_subagents() -> list[RLMSubagent]:
    """List direct RLM children retained by the current parent session."""
    payload = await host_request("rlm.list_subagents")
    entries = payload.get("subagents")
    if not isinstance(entries, list):
        raise RuntimeError("rlm.list_subagents returned an invalid subagents registry")
    return [_subagent_from_payload(entry) for entry in entries]


def _collect_target_selector(target: Any, what: str = "collect target") -> str:
    """Normalize a child selector: spawn handle, subagent row, or a name/id string."""
    if isinstance(target, RLMSpawnHandle):
        return target.rlm_child_id
    if isinstance(target, RLMSubagent):
        return target.rlm_child_id
    if isinstance(target, str) and target.strip():
        return target.strip()
    raise TypeError(
        f"{what} must be RLMSpawnHandle, RLMSubagent, or non-empty str, got {type(target).__name__}"
    )


def _child_result_from_payload(payload: Any) -> RLMChildResult:
    if not isinstance(payload, dict):
        raise RuntimeError("rlm.collect returned an invalid result entry")
    child_id = payload.get("rlm_child_id")
    if not isinstance(child_id, str) or not child_id:
        raise RuntimeError("rlm.collect entry is missing rlm_child_id")
    status = payload.get("status")
    if status not in {"queued", "running", "done", "error", "cancelled"}:
        raise RuntimeError("rlm.collect entry has invalid status")
    settled = payload.get("settled")
    if not isinstance(settled, bool):
        raise RuntimeError("rlm.collect entry has invalid settled flag")

    def _optional_str(field: str) -> str | None:
        value = payload.get(field)
        if value is None:
            return None
        if not isinstance(value, str):
            raise RuntimeError(f"rlm.collect entry has invalid {field}")
        return value

    def _optional_int(field: str) -> int | None:
        value = payload.get(field)
        if value is None:
            return None
        if not isinstance(value, int) or isinstance(value, bool):
            raise RuntimeError(f"rlm.collect entry has invalid {field}")
        return value

    session_dir = _optional_str("session_dir")
    replied = payload.get("replied_since_task")
    if replied is not None and not isinstance(replied, bool):
        raise RuntimeError("rlm.collect entry has invalid replied_since_task")
    return RLMChildResult(
        rlm_child_id=child_id,
        session_name=_optional_str("session_name"),
        session_dir=Path(session_dir) if session_dir else None,
        status=status,
        settled=settled,
        answer_preview=_optional_str("answer_preview"),
        error=_optional_str("error"),
        duration_ms=_optional_int("duration_ms"),
        tool_use_count=_optional_int("tool_use_count"),
        replied_since_task=replied,
        handback=_optional_str("handback"),
        acceptance=_optional_str("acceptance"),
    )


async def collect(
    targets: Any = None,
    *,
    timeout_ms: int = 0,
) -> list[RLMChildResult]:
    """Collect typed results from direct RLM children.

    ``targets`` selects children: spawn handles, subagent rows, name strings,
    or a list mixing all three. ``None`` (or an empty list) selects every
    direct child that is not being deleted.

    ``timeout_ms`` bounds the wait: 0 returns a non-blocking snapshot
    immediately; a positive value blocks only this kernel call until the
    first selected child settles (its result is the one to integrate) or
    the timeout elapses, and returns every selected child's current
    snapshot. A timeout is never an error. An input queued for this
    session meanwhile (a user message or steer, a peer's message) ends the
    wait first: the children keep running, their reports arrive later, and
    the message follows the cell's result. Completed children keep their
    result until deleted, so a later ``collect`` re-reads them without
    waiting.
    """
    if not isinstance(timeout_ms, int) or isinstance(timeout_ms, bool) or timeout_ms < 0:
        raise TypeError("timeout_ms must be a non-negative int")
    if targets is None:
        selectors: list[str] = []
    elif isinstance(targets, (RLMSpawnHandle, RLMSubagent, str)):
        selectors = [_collect_target_selector(targets)]
    elif isinstance(targets, (list, tuple)):
        selectors = [_collect_target_selector(target) for target in targets]
    else:
        raise TypeError(
            f"targets must be None, a target, or a list of targets, got {type(targets).__name__}"
        )
    payload = await host_request("rlm.collect", {"targets": selectors, "timeout_ms": timeout_ms})
    results = payload.get("results")
    if not isinstance(results, list):
        raise RuntimeError("rlm.collect returned an invalid results list")
    return [_child_result_from_payload(entry) for entry in results]


RLM_PROGRESS_NOTE_MAX_LENGTH = 512


async def progress_note(message: str) -> RLMProgressNoteResult:
    """Report brief in-flight progress to the parent orchestrator.

    The note (at most 512 UTF-16 code units, about one per 10 seconds) reaches the
    parent's child snapshots and roster entries without steering the parent
    or requiring an explicit reply. A throttled note returns
    ``accepted=False`` with a ``retry_after_ms`` hint instead of raising.
    """
    if not isinstance(message, str):
        raise TypeError(f"message must be str, got {type(message).__name__}")
    stripped = message.strip()
    if not stripped:
        raise ValueError("message must not be empty")
    # The host measures message.length in UTF-16 code units, so 512 astral
    # characters are 1024 units there and would fail its check after Python
    # accepted them. Measure the stripped message the same way; surrogatepass
    # counts a lone surrogate as one unit, matching the host's length.
    if len(stripped.encode("utf-16-le", "surrogatepass")) // 2 > RLM_PROGRESS_NOTE_MAX_LENGTH:
        raise ValueError(f"message must be at most {RLM_PROGRESS_NOTE_MAX_LENGTH} characters")
    payload = await host_request("rlm.progress.note", {"message": stripped})
    accepted = payload.get("accepted")
    if not isinstance(accepted, bool):
        raise RuntimeError("rlm.progress.note returned an invalid accepted flag")
    retry_after_ms = payload.get("retry_after_ms")
    if retry_after_ms is not None and (not isinstance(retry_after_ms, int) or isinstance(retry_after_ms, bool)):
        raise RuntimeError("rlm.progress.note returned an invalid retry_after_ms")
    return RLMProgressNoteResult(accepted=accepted, retry_after_ms=retry_after_ms)


async def delete_subagent(target: str | RLMSubagent | RLMSpawnHandle) -> RLMSubagent:
    """Delete one running or retained direct child from the current parent session.

    ``target`` selects the child: the spawn handle returned by ``rlm.spawn``, a
    subagent row from ``list_subagents()``, or a child id/session name string.
    """
    if isinstance(target, RLMSpawnHandle):
        selector = target.rlm_child_id
    elif isinstance(target, RLMSubagent):
        selector = target.rlm_child_id
    elif isinstance(target, str):
        selector = target.strip()
        if not selector:
            raise ValueError("target must not be empty")
    else:
        raise TypeError(
            f"target must be RLMSpawnHandle, RLMSubagent, or str, got {type(target).__name__}"
        )
    payload = await host_request("rlm.delete_subagent", {"target": selector})
    return _subagent_from_payload(payload.get("subagent"), "rlm.delete_subagent")


async def rename(new_name: str, *, session_id: str | RLMSpawnHandle | RLMSubagent | None = None) -> str:
    """Rename this session or one of its direct children.

    Omitting ``session_id`` renames the current session. A spawn handle, a
    ``list_subagents()`` row, or a session id string renames a direct child;
    child names are rejected. Names follow spawn rules, must be unique among
    siblings, and the renamed session sees a transcript notice.
    """
    if not isinstance(new_name, str):
        raise TypeError(f"new_name must be str, got {type(new_name).__name__}")
    payload: dict[str, Any] = {"name": new_name}
    if session_id is not None:
        payload["session_id"] = _collect_target_selector(session_id, "session_id")
    reply = await host_request("rlm.rename", payload)
    name = reply.get("name")
    if not isinstance(name, str):
        raise RuntimeError("rlm.rename returned an invalid name")
    return name


class _HarnessProxy:
    """Resolve the harness state against the current environment on every access.

    Session env vars may be applied after import, so a state bound at import
    time could freeze an env-less resolution. Resolution must never raise (a
    failure inside the kernel namespace would take down the kernel). When the
    local store is genuinely unconfigured (no session env, e.g. --no-session)
    reads see an empty view but local writes raise instructively instead of
    vanishing on kernel exit; any other resolution failure degrades to a shared
    in-memory store until local resolution starts succeeding.
    """

    _fallback: HarnessState | None = None
    _unpersisted: HarnessState | None = None

    def _resolve(self) -> HarnessState:
        try:
            return get_harness_state()
        except RuntimeError as exc:
            if "Local harness state requires" in str(exc):
                if _HarnessProxy._unpersisted is None:
                    _HarnessProxy._unpersisted = HarnessState(
                        in_memory=True,
                        local_write_error=(
                            f"{exc} This session has no persistent local harness store; "
                            "pass global_=True to persist across sessions."
                        ),
                    )
                return _HarnessProxy._unpersisted
            return self._degraded()
        except Exception:  # pragma: no cover - harness access must never raise
            return self._degraded()

    @staticmethod
    def _degraded() -> HarnessState:
        if _HarnessProxy._fallback is None:
            _HarnessProxy._fallback = HarnessState(in_memory=True)
        return _HarnessProxy._fallback

    def __getattr__(self, name: str) -> Any:
        # A chat-memory session's memory is the chat: its harness exposes
        # no memory or prompt-note method.
        if name in CHAT_MEMORY_ABSENT_METHODS and chat_memory_session():
            raise AttributeError(f"rlm.harness has no {name}: {CHAT_MEMORY_MESSAGE}")
        return getattr(self._resolve(), name)

    def __repr__(self) -> str:
        return repr(self._resolve())


_harness_state = _HarnessProxy()


class _RLMFactoryNamespace:
    """Run stored state-machine factories: rlm.factory.run/status/stop/resume,
    plus graph/watch for live monitoring.

    ``run('<spec_id>')`` validates a stored factory entry (machine form, or
    dag sugar that compiles to one), enters the entry states up to the
    spec's max_parallel, and returns immediately; a kernel asyncio task
    continues the run (nonblocking control loop). Runs live in kernel
    memory only; children stay supervisor-owned. Every call is async, so
    always await it: ``await rlm.factory.run('<id>')``.

    When no stored entry carries the id, ``run`` falls back to the machine
    library: the bundled seeds ship inside the runtime (the personal
    library lives under the agent dir), and the template runs directly
    without creating a harness entry:
    ``await rlm.factory.run('review-sweep')``.
    ``eukhe factory list | import | export`` manages the library (a
    broken machine names its exact errors; a missing one lists what the
    library has).

    ``graph()`` returns the machine structure fused with live runtime state
    (``status()``'s data plus the static graph): pass a live run id for one
    run's snapshot, a stored spec id for the static structure, or nothing
    for every live run. ``watch('<run_id>', timeout)`` blocks until the
    run's state/instance shape changes or the timeout elapses (bounded),
    then returns the same snapshot with ``changed`` — an agent can stream
    progress and drive orchestration programmatically, and the emitted
    graph model renders as ASCII or genuine Mermaid from one shape.

    The factory is opt-in: while the ``factory.enabled`` setting is off (the
    default; the user turns it on with ``/factory on``), every call above
    refuses with one clean message and only ``help()`` answers, so the
    guide stays readable before opting in.

    ``help()`` returns the full embedded authoring reference and API guide
    (states, ports, guards, joins, foreach, budgets, the machine library,
    and the API with worked examples): ``rlm.factory.help()``.
    """

    async def run(self, spec_id: str, *, name: str | None = None) -> dict[str, Any]:
        return await run_factory(spec_id, name=name)

    async def status(self, run_id: str) -> dict[str, Any]:
        return await status_factory(run_id)

    async def stop(self, run_id: str) -> dict[str, Any]:
        return await stop_factory(run_id)

    async def resume(self, run_id: str) -> dict[str, Any]:
        return await resume_factory(run_id)

    async def graph(self, ref: str | None = None) -> dict[str, Any]:
        return graph_factory(ref)

    async def watch(self, run_id: str, timeout: float = 0.0) -> dict[str, Any]:
        return await watch_factory(run_id, timeout)

    def help(self) -> str:
        """Return the embedded factory authoring reference and API guide."""
        return FACTORY_HELP


class _RLMNamespace:
    harness = _harness_state
    get_harness_state = staticmethod(get_harness_state)
    RLMQueryError = RLMQueryError
    RLMText = RLMText

    async def spawn(
        self,
        prompt: str,
        *,
        name: str,
        model: str | None = None,
        thinking: str | None = None,
        budget: dict[str, Any] | None = None,
        accept: list[dict[str, Any]] | None = None,
        accept_intent: bool | None = None,
        accept_returns: int | None = None,
    ) -> RLMSpawnHandle:
        return await spawn(
            prompt,
            name=name,
            model=model,
            thinking=thinking,
            budget=budget,
            accept=accept,
            accept_intent=accept_intent,
            accept_returns=accept_returns,
        )

    async def split(
        self,
        left: dict[str, Any],
        right: dict[str, Any],
        own: list[str] | None = None,
        hold: int | None = None,
    ) -> tuple[RLMSpawnHandle, RLMSpawnHandle]:
        return await split(left, right, own=own, hold=hold)

    async def find_models(self, query: str = "", limit: int = 8) -> list[RLMModel]:
        return await find_models(query, limit)

    async def list_subagents(self) -> list[RLMSubagent]:
        return await list_subagents()

    async def progress_note(self, message: str) -> RLMProgressNoteResult:
        return await progress_note(message)

    async def delete_subagent(self, target: str | RLMSubagent | RLMSpawnHandle) -> RLMSubagent:
        return await delete_subagent(target)

    async def rename(
        self,
        new_name: str,
        *,
        session_id: str | RLMSpawnHandle | RLMSubagent | None = None,
    ) -> str:
        return await rename(new_name, session_id=session_id)

    async def collect(self, targets: Any = None, *, timeout_ms: int = 0) -> list[RLMChildResult]:
        return await collect(targets, timeout_ms=timeout_ms)

    async def query(
        self,
        prompt: str,
        context: str | None = None,
        *,
        model: str | None = None,
        thinking: str | None = None,
        max_bytes: int | None = None,
    ) -> RLMText:
        return await query(prompt, context, model=model, thinking=thinking, max_bytes=max_bytes)

    async def query_batch(
        self, calls: list[dict[str, Any]], *, concurrency: int | None = None
    ) -> list[RLMText | RLMQueryError]:
        return await query_batch(calls, concurrency=concurrency)

    factory = _RLMFactoryNamespace()

    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        raise TypeError(_NOT_CALLABLE_MESSAGE)

    # AttributeError keeps hasattr() semantics intact while still naming the replacement.
    def __getattr__(self, name: str) -> Any:
        if name == "run":
            raise AttributeError(_RENAMED_RUN_MESSAGE)
        raise AttributeError(f"'rlm' object has no attribute {name!r}")


rlm = _RLMNamespace()
harness = _harness_state


class _NotCallableModule(types.ModuleType):
    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        raise TypeError(_NOT_CALLABLE_MESSAGE)


sys.modules[__name__].__class__ = _NotCallableModule

__all__ = [
    "BashHandle",
    "BashResult",
    "ChatLine",
    "HarnessEntry",
    "HarnessScope",
    "HarnessState",
    "HistoryEntry",
    "McpIntegration",
    "McpToolError",
    "NotEnabled",
    "RLMModel",
    "RLMProgressNoteResult",
    "RLMQueryError",
    "RLMSpawnHandle",
    "RLMSubagent",
    "RLMSubagentActivity",
    "RLMText",
    "ToolCall",
    "RefinementEvent",
    "Job",
    "bash",
    "chat",
    "delete_subagent",
    "emit",
    "find_models",
    "get_harness_state",
    "harness",
    "history",
    "host_request",
    "jobs",
    "host_request_sync",
    "list_subagents",
    "progress_note",
    "query",
    "query_batch",
    "remote",
    "rename",
    "rlm",
    "spawn",
    "split",
]

# Lazily re-export the MCP base class. Kept lazy so `import rlm` never requires
# the optional `mcp` SDK — only integration packages that subclass it do.
_LAZY_MCP = {"McpIntegration", "McpToolError", "NotEnabled"}


def __getattr__(name: str) -> Any:  # noqa: D401 - module-level lazy attr hook
    if name in _LAZY_MCP:
        from . import mcp_base

        return getattr(mcp_base, name)
    if name == "run":
        raise AttributeError(_RENAMED_RUN_MESSAGE)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
