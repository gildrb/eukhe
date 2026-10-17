"""Documents from the kernel: ``read``, ``write`` (and, sharing the same
session edit store, ``grep``, ``glob``, ``edit``).

Every function is synchronous and resolves relative paths against the
kernel's current directory. Each takes the arguments of the wire tool of the
same name (positionally in the order shown, or by keyword), and the host
decodes them by that tool's contract: the same aliases (``file_path`` ->
``path``), scalar spellings (``"false"`` -> ``False``), and refusals, each
repair reported in the result's ``warnings``. Results print as the
model-facing projection (``[path#TAG]`` then ``N:TEXT`` rows) and keep the
typed fields. Rejections, including arguments no repair can fix, raise
:class:`FsError`.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import Any

__all__ = [
    "Doc",
    "EditRejected",
    "EditResult",
    "FsError",
    "Hit",
    "Hits",
    "Paths",
    "WriteResult",
    "edit",
    "glob",
    "grep",
    "read",
    "write",
]


class FsError(Exception):
    """A rejected document operation; ``str(error)`` teaches the fix.

    ``reason`` is a stable code (``arguments``, ``not_found``, ``selector``, ...),
    ``version`` the function revision that produced it (``read@1``).
    """

    def __init__(self, version: str, reason: str, message: str) -> None:
        super().__init__(message)
        self.version = version
        self.reason = reason
        self.message = message


class EditRejected(FsError):
    """An ``edit`` that changed nothing. ``reason``: ``arguments`` (no repair
    fits, e.g. old/new strings), ``parse`` (bad grammar), ``anchor`` (a line
    not shown by ``read``/``grep``), ``apply`` (stale tag, no-op loop, file
    changed meanwhile), or ``io``. The message names the fix."""


def _call(name: str, positional: tuple[str, ...], args: tuple[Any, ...], kwargs: dict[str, Any]) -> dict[str, Any]:
    """Send ``name``'s arguments as given; the host repairs and checks them."""
    from . import host_request_sync

    if len(args) > len(positional):
        raise TypeError(f"{name}() takes at most {len(positional)} positional arguments ({len(args)} given)")
    sent = dict(zip(positional, args))
    for key, value in kwargs.items():
        if key in sent:
            raise TypeError(f"{name}() got multiple values for argument {key!r}")
        sent[key] = value
    reply = host_request_sync(f"fs.{name}", {"cwd": os.getcwd(), "args": sent})
    if reply.get("outcome") == "rejected":
        error = EditRejected if name == "edit" else FsError
        raise error(reply["version"], reply["reason"], reply["message"])
    return reply


def _with_warnings(rendered: str, warnings: list[str]) -> str:
    if not warnings:
        return rendered
    return rendered + "\nWarnings:\n" + "\n".join(f"- {warning}" for warning in warnings)


@dataclass(frozen=True)
class Doc:
    """A read file or directory, or an internal URL read as text (``kind``
    ``"text"``, ``absolute`` None). ``text`` is the whole file (LF, no BOM);
    ``header`` is the ``[path#TAG]`` an edit section starts with."""

    version: str
    path: str
    absolute: str | None
    kind: str
    rendered: str
    diags: list[str]
    tag: str | None = None
    text: str = ""
    total_lines: int = 0
    shown: list[tuple[int, int]] = field(default_factory=list)
    entries: list[dict[str, Any]] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def lines(self) -> list[str]:
        lines = self.text.split("\n")
        if self.text.endswith("\n"):
            lines.pop()
        return lines

    @property
    def header(self) -> str | None:
        return None if self.tag is None else f"[{self.path}#{self.tag}]"

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


@dataclass(frozen=True)
class WriteResult:
    """A committed whole-file write."""

    version: str
    path: str
    absolute: str
    created: bool
    bytes: int
    tag: str | None
    made_executable: bool
    rendered: str
    warnings: list[str] = field(default_factory=list)

    @property
    def header(self) -> str | None:
        return None if self.tag is None else f"[{self.path}#{self.tag}]"

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


@dataclass(frozen=True)
class EditResult:
    """A committed edit. ``files`` holds one dict per section (``path``,
    ``change``, ``diff``, ``warnings``, ``tag``); ``header`` of the last file
    is the ``[path#TAG]`` the next edit of it starts with."""

    version: str
    rendered: str
    files: list[dict[str, Any]]
    warnings: list[str] = field(default_factory=list)

    @property
    def headers(self) -> list[str]:
        return [f"[{file['path']}#{file['tag']}]" for file in self.files if file.get("tag")]

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


@dataclass(frozen=True)
class Hit:
    """One matching line; ``line`` is an anchor for ``edit``."""

    path: str
    tag: str | None
    line: int
    text: str


class Hits(list):
    """``grep`` hits: a list of :class:`Hit` that prints as the tagged rows."""

    def __init__(
        self, hits: list[Hit], version: str, rendered: str, total_files: int, more_files: bool, warnings: list[str]
    ) -> None:
        super().__init__(hits)
        self.version = version
        self.rendered = rendered
        self.total_files = total_files
        self.more_files = more_files
        self.warnings = warnings

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


class Paths(list):
    """``glob`` matches: a list of paths, newest first, that prints as the
    folded listing."""

    def __init__(self, paths: list[str], version: str, rendered: str, truncated: bool, warnings: list[str]) -> None:
        super().__init__(paths)
        self.version = version
        self.rendered = rendered
        self.truncated = truncated
        self.warnings = warnings

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


def read(*args: Any, **kwargs: Any) -> Doc:
    """``read(path)``: read a file or directory (``read@1``).

    ``path`` may carry a selector: ``"src/a.rs:50-120"``, ``":N+K"``,
    ``":raw"``. A file prints as ``[path#TAG]`` plus ``N:TEXT`` rows; the
    shown lines become editable anchors. Internal URLs: ``repo://<path>``,
    ``skill://<name>/<path>``, ``agent://<name|id>``, ``memory://[<id>[/<n>]]``
    (``mcp://`` is the wire tool's; here use ``await mcp.read_resource``);
    a ``..`` above a URL's root, or a symlink out of it, is rejected.
    """
    reply = _call("read", ("path",), args, kwargs)
    return Doc(
        version=reply["version"],
        path=reply["path"],
        absolute=reply["absolute"],
        kind=reply["kind"],
        rendered=reply["rendered"],
        diags=reply["diags"],
        tag=reply.get("tag"),
        text=reply.get("text", ""),
        total_lines=reply.get("total_lines", 0),
        shown=[(start, end) for start, end in reply.get("shown", [])],
        entries=reply.get("entries", []),
        warnings=reply["warnings"],
    )


def write(*args: Any, **kwargs: Any) -> WriteResult:
    """``write(path, content)``: create or overwrite a file atomically
    (``write@1``).

    Parent directories are created. A replaced file keeps its BOM, line
    endings, and mode. Prefer ``edit`` for changes to an existing file.
    """
    reply = _call("write", ("path", "content"), args, kwargs)
    return WriteResult(
        version=reply["version"],
        path=reply["path"],
        absolute=reply["absolute"],
        created=reply["created"],
        bytes=reply["bytes"],
        tag=reply["tag"],
        made_executable=reply["made_executable"],
        rendered=reply["rendered"],
        warnings=reply["warnings"],
    )


def edit(*args: Any, **kwargs: Any) -> EditResult:
    """``edit(input)``: apply a hashline payload (``edit@hl.1``), the grammar
    of the ``edit`` tool: ``[path#TAG]`` sections of ``PUT``/``CUT``/``REM``/``MV``
    ops whose line numbers come from the latest ``read``/``grep``/edit result.

    For programmatic edits (loops, codemods); raises :class:`EditRejected`.
    """
    reply = _call("edit", ("input",), args, kwargs)
    return EditResult(version=reply["version"], rendered=reply["rendered"], files=reply["files"], warnings=reply["warnings"])


def grep(*args: Any, **kwargs: Any) -> Hits:
    """``grep(pattern, path=".", *, case=True, gitignore=True, skip=0)``:
    search files with a Rust regex (``grep@1``).

    ``path`` is a file, directory, glob, or ``file:lines`` selector; ``;``
    separates several. Prints ``[path#TAG]`` groups of ``*N:TEXT`` (match)
    and `` N:TEXT`` (context) rows; every printed line becomes an ``edit``
    anchor. Results page by file: pass ``skip`` from the pagination notice.
    """
    reply = _call("grep", ("pattern", "path"), args, kwargs)
    hits = [
        Hit(path=file["path"], tag=file["tag"], line=line, text=text)
        for file in reply["files"]
        for line, text in file["matches"]
    ]
    return Hits(hits, reply["version"], reply["rendered"], reply["total_files"], reply["more_files"], reply["warnings"])


def glob(*args: Any, **kwargs: Any) -> Paths:
    """``glob(path=".", *, hidden=True, gitignore=True, limit=None)``: list
    paths matching globs (``glob@1``), newest first. ``;`` separates several
    (``"src/**/*.rs; tests/*.rs"``); a bare ``*.rs`` matches at any depth.
    """
    reply = _call("glob", ("path",), args, kwargs)
    return Paths(reply["paths"], reply["version"], reply["rendered"], reply["truncated"], reply["warnings"])
