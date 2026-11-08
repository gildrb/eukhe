"""Sub-model calls over data: ``rlm.query`` and ``rlm.query_batch``.

The Recursive Language Model move: long material stays in the REPL as
data, and the model calls a sub-model on a slice of it. Each query is one
tool-less model call (no tools, no session, no transcript entry); its
answer comes back as a Python value and reaches the conversation only if
the cell prints it. The host admits a batch whole (the session's query
concurrency cap and byte budget) and runs it in waves; each call's usage
counts into the session's usage.
"""

from __future__ import annotations

from typing import Any

#: The keys a ``query_batch`` call may carry.
_CALL_KEYS = frozenset({"prompt", "context", "model", "thinking", "max_bytes"})


class RLMQueryError(RuntimeError):
    """A query that produced no answer: a refused batch (raised), or one
    failed call of a batch (returned in its place)."""


class RLMText(str):
    """A query's answer: the text itself (a ``str``), plus ``truncated``
    (``max_bytes`` cut it at a character boundary) and ``model`` (the
    ``provider/id`` that answered)."""

    truncated: bool
    model: str

    def __new__(cls, text: str, *, truncated: bool, model: str) -> RLMText:
        value = super().__new__(cls, text)
        value.truncated = truncated
        value.model = model
        return value


def _optional_str(call: dict[str, Any], key: str, index: int) -> str | None:
    value = call.get(key)
    if value is not None and not isinstance(value, str):
        raise TypeError(f"query {index}: {key} must be str or None, got {type(value).__name__}")
    return value


def _positive_int(value: Any, what: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise TypeError(f"{what} must be a positive int, got {value!r}")
    return value


def _payload(calls: list[dict[str, Any]], concurrency: int | None) -> dict[str, Any]:
    """The host request: each call with its context as an index into one
    list of distinct contexts (a context shared by many prompts crosses
    once)."""
    if not isinstance(calls, list) or not calls:
        raise TypeError("calls must be a non-empty list of dicts")
    contexts: list[str] = []
    seen: dict[str, int] = {}
    entries: list[dict[str, Any]] = []
    for index, call in enumerate(calls):
        if not isinstance(call, dict):
            raise TypeError(f"query {index}: each call must be a dict, got {type(call).__name__}")
        unknown = sorted(set(call) - _CALL_KEYS)
        if unknown:
            raise TypeError(f"query {index}: unsupported keys: {', '.join(unknown)}")
        prompt = call.get("prompt")
        if not isinstance(prompt, str):
            raise TypeError(f"query {index}: prompt must be str, got {type(prompt).__name__}")
        entry: dict[str, Any] = {"prompt": prompt}
        context = _optional_str(call, "context", index)
        if context is not None:
            if context not in seen:
                seen[context] = len(contexts)
                contexts.append(context)
            entry["context"] = seen[context]
        for key in ("model", "thinking"):
            value = _optional_str(call, key, index)
            if value is not None:
                entry[key] = value
        max_bytes = call.get("max_bytes")
        if max_bytes is not None:
            entry["max_bytes"] = _positive_int(max_bytes, f"query {index}: max_bytes")
        entries.append(entry)
    payload: dict[str, Any] = {"calls": entries, "contexts": contexts}
    if concurrency is not None:
        payload["concurrency"] = _positive_int(concurrency, "concurrency")
    return payload


def _result(index: int, value: Any) -> RLMText | RLMQueryError:
    if not isinstance(value, dict):
        raise RuntimeError(f"rlm.query_batch returned an invalid result {index}")
    error = value.get("error")
    if isinstance(error, str):
        return RLMQueryError(error)
    text = value.get("text")
    truncated = value.get("truncated")
    model = value.get("model")
    if not isinstance(text, str) or not isinstance(truncated, bool) or not isinstance(model, str):
        raise RuntimeError(f"rlm.query_batch returned an invalid result {index}")
    return RLMText(text, truncated=truncated, model=model)


async def query_batch(
    calls: list[dict[str, Any]], *, concurrency: int | None = None
) -> list[RLMText | RLMQueryError]:
    """Run several tool-less model calls; answers come back in order.

    Each call is a dict ``{"prompt": str, "context"?: str | None, "model"?:
    str, "thinking"?: str, "max_bytes"?: int}`` as in :func:`query`. At most
    ``concurrency`` calls (default and ceiling: the free part of the
    session's ``rlm.queryConcurrency`` cap) run at once. A failed call
    gives an ``RLMQueryError`` in its place; a refused batch (over the
    session's ``rlm.queryBudgetBytes``, or the cap already full) raises
    ``RLMQueryError`` and runs nothing.
    """
    from . import host_request

    payload = _payload(calls, concurrency)
    reply = await host_request("rlm.query_batch", payload)
    refused = reply.get("refused")
    if isinstance(refused, str):
        raise RLMQueryError(refused)
    results = reply.get("results")
    if not isinstance(results, list) or len(results) != len(payload["calls"]):
        raise RuntimeError("rlm.query_batch returned an invalid results list")
    return [_result(index, value) for index, value in enumerate(results)]


async def query(
    prompt: str,
    context: str | None = None,
    *,
    model: str | None = None,
    thinking: str | None = None,
    max_bytes: int | None = None,
) -> RLMText:
    """Ask a sub-model about ``context`` and get its answer as a ``str``.

    One model call without tools, session or transcript entry: the answer
    reaches the conversation only if the cell prints it. ``model``: an
    exact ``provider/id`` (default: the ``rlm.queryModel`` setting, else
    the session's model). ``thinking``: a reasoning level (default: the
    model's own). ``max_bytes``: cut the answer to at most that many UTF-8
    bytes at a character boundary (``.truncated`` says so). Raises
    ``RLMQueryError`` when the call fails or is refused.
    """
    call: dict[str, Any] = {"prompt": prompt, "context": context, "model": model, "thinking": thinking}
    if max_bytes is not None:
        call["max_bytes"] = max_bytes
    (result,) = await query_batch([call])
    if isinstance(result, RLMQueryError):
        raise result
    return result
