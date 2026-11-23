"""This conversation as REPL data: ``history`` and ``chat``.

Reads return Python values and print nothing, so code can slice, filter
and hand them to ``rlm.query`` without spending context on them.

- ``history``: a session without chat memory reads its own durable
  transcript, compactions included, so what a compaction summarized away
  stays readable.
- ``chat``: a chat-memory session reads its memory the way the ``zoom``
  tool does: the view's lines, a line's two halves, a message whole. It
  has no search: the chat memory is read by zoom only.

The host answers each read for the calling cell's conversation and
refuses the object that does not fit the session's memory with a message
naming the one that does. Both are synchronous: call them without
``await``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, NamedTuple

#: The page size of ``history.entries`` requests.
_PAGE = 256


@dataclass(frozen=True)
class ToolCall:
    """A tool call of an assistant entry."""

    id: str
    name: str
    arguments: dict[str, Any]


@dataclass(frozen=True)
class HistoryEntry:
    """One durable transcript entry, oldest first by ``id``.

    ``kind``: ``user``, ``assistant``, ``tool_result``, ``compaction``,
    ``reset``, ``system``, ``bash``, ``custom`` or the raw durable kind.
    ``text``: what the entry said (a compaction: its summary; a tool
    result: its output). ``tool_calls``: an assistant entry's calls.
    ``tool_call_id``/``tool_name``/``is_error``: a tool result's.
    ``custom_type``: a custom entry's type. ``first_kept_id``: the first
    entry a compaction or reset kept. ``timestamp``: Unix ms, when known.
    """

    id: int
    kind: str
    text: str
    tool_calls: tuple[ToolCall, ...] = ()
    tool_call_id: str | None = None
    tool_name: str | None = None
    is_error: bool | None = None
    custom_type: str | None = None
    first_kept_id: int | None = None
    timestamp: int | None = None


class ChatLine(NamedTuple):
    """One line of the chat memory: the ``n`` messages from ``id`` on,
    summarized in ``text``."""

    id: int
    n: int
    text: str


def _request(request_type: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    from . import host_request_sync

    return host_request_sync(request_type, payload)


def _optional(value: Any, kind: type, what: str) -> Any:
    if value is not None and not isinstance(value, kind):
        raise RuntimeError(f"{what} is not a {kind.__name__}")
    return value


def _entry(value: Any) -> HistoryEntry:
    if not isinstance(value, dict):
        raise RuntimeError("history returned an invalid entry")
    entry_id = value.get("id")
    kind = value.get("kind")
    text = value.get("text")
    if not isinstance(entry_id, int) or not isinstance(kind, str) or not isinstance(text, str):
        raise RuntimeError("history returned an invalid entry")
    calls = []
    for call in value.get("tool_calls") or []:
        if not isinstance(call, dict) or not isinstance(call.get("id"), str) or not isinstance(call.get("name"), str):
            raise RuntimeError("history returned an invalid tool call")
        arguments = call.get("arguments")
        calls.append(ToolCall(call["id"], call["name"], arguments if isinstance(arguments, dict) else {}))
    return HistoryEntry(
        id=entry_id,
        kind=kind,
        text=text,
        tool_calls=tuple(calls),
        tool_call_id=_optional(value.get("tool_call_id"), str, "tool_call_id"),
        tool_name=_optional(value.get("tool_name"), str, "tool_name"),
        is_error=_optional(value.get("is_error"), bool, "is_error"),
        custom_type=_optional(value.get("custom_type"), str, "custom_type"),
        first_kept_id=_optional(value.get("first_kept_id"), int, "first_kept_id"),
        timestamp=_optional(value.get("timestamp"), int, "timestamp"),
    )


def _id(value: Any, what: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise TypeError(f"{what} must be a non-negative int, got {value!r}")
    return value


class _History:
    """This conversation's durable history (sessions without chat memory)."""

    def entries(self, *, kind: str | None = None) -> list[HistoryEntry]:
        """Every entry of this conversation, oldest first, compactions and
        what they summarized included; ``kind`` keeps one kind."""
        if kind is not None and not isinstance(kind, str):
            raise TypeError(f"kind must be str or None, got {type(kind).__name__}")
        entries: list[HistoryEntry] = []
        after: int | None = None
        while True:
            payload: dict[str, Any] = {"limit": _PAGE}
            if after is not None:
                payload["after"] = after
            if kind is not None:
                payload["kind"] = kind
            reply = _request("history.entries", payload)
            page = reply.get("entries")
            if not isinstance(page, list):
                raise RuntimeError("history.entries returned an invalid page")
            entries.extend(_entry(value) for value in page)
            after = _optional(reply.get("next"), int, "history.entries next")
            if after is None:
                return entries

    def entry(self, id: int) -> HistoryEntry:
        """The entry ``id`` of this conversation."""
        reply = _request("history.entry", {"id": _id(id, "id")})
        return _entry(reply.get("entry"))

    def compactions(self) -> list[HistoryEntry]:
        """The compaction entries, oldest first: each one's summary is its
        ``text``; the entries before its ``first_kept_id`` are what it
        summarized."""
        return self.entries(kind="compaction")

    def __repr__(self) -> str:
        return "<history: history.entries(), history.entry(id), history.compactions()>"


def _lines(value: Any, what: str) -> list[ChatLine]:
    if not isinstance(value, list):
        raise RuntimeError(f"{what} returned invalid lines")
    lines = []
    for line in value:
        if (
            not isinstance(line, dict)
            or not isinstance(line.get("id"), int)
            or not isinstance(line.get("n"), int)
            or not isinstance(line.get("text"), str)
        ):
            raise RuntimeError(f"{what} returned an invalid line")
        lines.append(ChatLine(line["id"], line["n"], line["text"]))
    return lines


class _Chat:
    """The chat memory, read by zoom (chat-memory sessions)."""

    def view(self) -> list[ChatLine]:
        """The view the model sees: one ``(id, n, text)`` line per part,
        oldest first."""
        return _lines(_request("chat.view").get("lines"), "chat.view")

    def zoom(self, id: int, n: int) -> list[ChatLine]:
        """The two lines line ``(id, n)`` was built from (``n`` > 1)."""
        n = _id(n, "n")
        if n < 2:
            raise ValueError("n must be at least 2: chat.message(id) reads one message whole")
        return _lines(_request("chat.zoom", {"id": _id(id, "id"), "n": n}).get("lines"), "chat.zoom")

    def message(self, id: int) -> str:
        """Message ``id`` whole, as ``kind: text``."""
        text = _request("chat.zoom", {"id": _id(id, "id"), "n": 1}).get("text")
        if not isinstance(text, str):
            raise RuntimeError("chat.zoom returned no message text")
        return text

    def __getattr__(self, name: str) -> Any:
        if name == "search":
            raise AttributeError("chat has no search: the chat memory is read by zoom only (chat.view(), chat.zoom(id, n))")
        raise AttributeError(f"'chat' object has no attribute {name!r}")

    def __repr__(self) -> str:
        return "<chat: chat.view(), chat.zoom(id, n), chat.message(id)>"


history = _History()
chat = _Chat()
