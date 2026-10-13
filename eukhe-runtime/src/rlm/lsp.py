"""Language servers from the REPL (``lsp@1``).

Every function is async and asks the session's language servers through the
host (``rlm.host_request("lsp.<op>", ...)``). Servers are local executables
started on first use. Positions name a 1-based ``line`` and a ``symbol`` on
that line: ``"name"``, or ``"name#N"`` for its Nth match. Relative paths
resolve against ``os.getcwd()``. Failures raise ``RuntimeError`` with the
host's message.
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Any, Iterator


@dataclass(frozen=True)
class Location:
    path: str
    line: int
    column: int
    end_line: int
    end_column: int
    text: str


@dataclass(frozen=True)
class Diag:
    path: str
    line: int
    column: int
    end_line: int
    end_column: int
    severity: str
    message: str
    source: str | None
    code: str | None
    server: str


@dataclass(frozen=True)
class Diagnostics:
    """Diagnostics, and the servers whose fresh diagnostics had not arrived."""

    items: list[Diag]
    pending: list[str]

    @property
    def complete(self) -> bool:
        return not self.pending

    def __iter__(self) -> Iterator[Diag]:
        return iter(self.items)

    def __len__(self) -> int:
        return len(self.items)


@dataclass(frozen=True)
class Symbol:
    name: str
    kind: str
    container: str | None
    path: str
    line: int
    column: int


@dataclass(frozen=True)
class Action:
    index: int
    title: str
    kind: str | None
    preferred: bool
    server: str


@dataclass(frozen=True)
class Server:
    name: str
    state: str
    file_types: list[str]
    detail: str | None


@dataclass(frozen=True)
class FileChange:
    """One file of a workspace edit. Once written, ``diagnostics`` holds what
    the servers reported in the inline window (``None`` before), and
    ``diagnostics_complete`` says whether every server answered; the rest
    arrive as a ``[late-diagnostics]`` message. ``error``: the LSP host
    could not be told about the write."""

    path: str
    edits: int
    diagnostics: list[Diag] | None
    diagnostics_complete: bool
    error: str | None


@dataclass(frozen=True)
class RenameResult:
    files: list[FileChange]
    applied: bool


@dataclass(frozen=True)
class CodeActions:
    actions: list[Action]
    applied: Action | None
    files: list[FileChange]

    def __iter__(self) -> Iterator[Action]:
        return iter(self.actions)

    def __len__(self) -> int:
        return len(self.actions)


async def _request(op: str, **payload: Any) -> Any:
    from . import host_request

    return await host_request(f"lsp.{op}", {"cwd": os.getcwd(), **payload})


def _location(row: dict[str, Any]) -> Location:
    span = row["span"]
    return Location(
        path=row["path"],
        line=span["start"]["line"],
        column=span["start"]["column"],
        end_line=span["end"]["line"],
        end_column=span["end"]["column"],
        text=row["lineText"],
    )


def _diag(row: dict[str, Any]) -> Diag:
    span = row["span"]
    return Diag(
        path=row["path"],
        line=span["start"]["line"],
        column=span["start"]["column"],
        end_line=span["end"]["line"],
        end_column=span["end"]["column"],
        severity=row["severity"],
        message=row["message"],
        source=row["source"],
        code=row["code"],
        server=row["server"],
    )


def _diagnostics(report: dict[str, Any]) -> Diagnostics:
    return Diagnostics(items=[_diag(row) for row in report["diagnostics"]], pending=list(report["pending"]))


def _action(row: dict[str, Any]) -> Action:
    return Action(
        index=row["index"],
        title=row["title"],
        kind=row["kind"],
        preferred=row["preferred"],
        server=row["server"],
    )


def _changes(rows: list[dict[str, Any]]) -> list[FileChange]:
    return [
        FileChange(
            path=row["path"],
            edits=row["edits"],
            diagnostics=[_diag(item) for item in row["diagnostics"]] if "diagnostics" in row else None,
            diagnostics_complete=row.get("diagnostics_complete", False),
            error=row.get("diagnostics_error"),
        )
        for row in rows
    ]


async def diagnostics(path: str = "*") -> Diagnostics:
    """Current diagnostics of one file (synchronized from disk first) or, with ``"*"``, of every file the running servers know."""
    return _diagnostics(await _request("diagnostics", path=path))


async def definition(path: str, line: int, symbol: str) -> list[Location]:
    return [_location(row) for row in await _request("definition", path=path, line=line, symbol=symbol)]


async def type_definition(path: str, line: int, symbol: str) -> list[Location]:
    return [_location(row) for row in await _request("type_definition", path=path, line=line, symbol=symbol)]


async def implementation(path: str, line: int, symbol: str) -> list[Location]:
    return [_location(row) for row in await _request("implementation", path=path, line=line, symbol=symbol)]


async def references(path: str, line: int, symbol: str) -> list[Location]:
    return [_location(row) for row in await _request("references", path=path, line=line, symbol=symbol)]


async def hover(path: str, line: int, symbol: str) -> str | None:
    return await _request("hover", path=path, line=line, symbol=symbol)


async def symbols(path: str = "*", query: str | None = None) -> list[Symbol]:
    """Symbols of one file, or workspace symbols matching ``query`` with ``"*"``."""
    rows = await _request("symbols", path=path, query=query)
    return [
        Symbol(
            name=row["name"],
            kind=row["kind"],
            container=row["container"],
            path=row["location"]["path"],
            line=row["location"]["span"]["start"]["line"],
            column=row["location"]["span"]["start"]["column"],
        )
        for row in rows
    ]


async def rename(path: str, line: int, symbol: str, new_name: str, *, apply: bool = True) -> RenameResult:
    """Rename across the workspace; writes the edits unless ``apply=False``."""
    if not isinstance(apply, bool):
        raise TypeError("apply must be a bool")
    result = await _request("rename", path=path, line=line, symbol=symbol, new_name=new_name, apply=apply)
    return RenameResult(files=_changes(result["files"]), applied=result["applied"])


async def code_actions(path: str, line: int, symbol: str, *, apply: str | int | None = None) -> CodeActions:
    """List the code actions at a position; ``apply`` (index or title substring) applies one."""
    if isinstance(apply, bool) or not isinstance(apply, (str, int, type(None))):
        raise TypeError("apply must be an action index, a title substring, or None")
    result = await _request("code_actions", path=path, line=line, symbol=symbol, apply=apply)
    applied = result["applied"]
    return CodeActions(
        actions=[_action(row) for row in result["actions"]],
        applied=_action(applied) if applied is not None else None,
        files=_changes(result["files"]),
    )


async def status() -> list[Server]:
    """Every server whose root markers match the session's project, with its state."""
    return [
        Server(name=row["name"], state=row["state"], file_types=list(row["fileTypes"]), detail=row["detail"])
        for row in await _request("status")
    ]
