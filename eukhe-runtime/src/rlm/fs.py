"""Documents from the kernel: ``read``, ``write`` (and, sharing the same
session edit store, ``grep``, ``glob``, ``edit``).

Every function is synchronous and resolves relative paths against the
kernel's current directory. Results print as the model-facing projection
(``[path#TAG]`` then ``N:TEXT`` rows) and keep the typed fields. Argument
dialect is repaired charitably (aliases such as ``file_path`` -> ``path``,
``"true"`` -> ``True``, ``"3"`` -> ``3``); each repair is reported in the
result's ``warnings``. Semantic errors raise :class:`FsError`.
"""

from __future__ import annotations

import functools
import inspect
import os
import typing
from dataclasses import dataclass, field
from typing import Any, Callable, TypeVar

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

    ``reason`` is a stable code (``not_found``, ``selector``, ``binary``, ...),
    ``version`` the function revision that produced it (``read@1``).
    """

    def __init__(self, version: str, reason: str, message: str) -> None:
        super().__init__(message)
        self.version = version
        self.reason = reason
        self.message = message


class EditRejected(FsError):
    """An ``edit`` that changed nothing. ``reason``: ``parse`` (bad grammar),
    ``anchor`` (a line not shown by ``read``/``grep``), ``apply`` (stale tag,
    no-op loop, file changed meanwhile), or ``io``. The message names the fix."""


def _call(request_type: str, payload: dict[str, Any]) -> dict[str, Any]:
    from . import host_request_sync

    reply = host_request_sync(request_type, {**payload, "cwd": os.getcwd()})
    if reply.get("outcome") == "rejected":
        error = EditRejected if request_type == "fs.edit" else FsError
        raise error(reply["version"], reply["reason"], reply["message"])
    return reply


def _with_warnings(rendered: str, warnings: list[str]) -> str:
    if not warnings:
        return rendered
    return rendered + "\nWarnings:\n" + "\n".join(f"- {warning}" for warning in warnings)


@dataclass(frozen=True)
class Doc:
    """A read file or directory. ``text`` is the whole file (LF, no BOM);
    ``header`` is the ``[path#TAG]`` an edit section starts with."""

    version: str
    path: str
    absolute: str
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

    def __init__(self, hits: list[Hit], version: str, rendered: str, total_files: int, more_files: bool) -> None:
        super().__init__(hits)
        self.version = version
        self.rendered = rendered
        self.total_files = total_files
        self.more_files = more_files
        self.warnings: list[str] = []

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


class Paths(list):
    """``glob`` matches: a list of paths, newest first, that prints as the
    folded listing."""

    def __init__(self, paths: list[str], version: str, rendered: str, truncated: bool) -> None:
        super().__init__(paths)
        self.version = version
        self.rendered = rendered
        self.truncated = truncated
        self.warnings: list[str] = []

    def __str__(self) -> str:
        return _with_warnings(self.rendered, self.warnings)

    __repr__ = __str__


_F = TypeVar("_F", bound=Callable[..., Any])

_TRUE = {"true", "yes", "1", "on"}
_FALSE = {"false", "no", "0", "off"}


def _coerce(name: str, value: Any, hint: Any, repairs: list[str]) -> Any:
    """Repair a string spelling of a declared bool/int; leave the rest."""
    if not isinstance(value, str):
        return value
    accepted = typing.get_args(hint) or (hint,)
    if bool in accepted and value.strip().lower() in _TRUE | _FALSE:
        repaired = value.strip().lower() in _TRUE
        repairs.append(f"{name}={value!r} read as {repaired!r}")
        return repaired
    if int in accepted and value.strip().lstrip("-").isdigit():
        repaired = int(value.strip())
        repairs.append(f"{name}={value!r} read as {repaired!r}")
        return repaired
    return value


def charitable(
    aliases: dict[str, tuple[str, ...]], refused: dict[str, str] | None = None
) -> Callable[[_F], _F]:
    """Strict on meaning, charitable on dialect (omp ADR 0020).

    ``aliases`` maps a parameter to the names models also use for it. A
    repaired call proceeds and its result carries one warning per repair.
    ``refused`` maps keywords of another dialect to the hint that teaches
    this one; they and any unknown keyword raise TypeError.
    """
    refusals = refused or {}

    def decorate(function: _F) -> _F:
        signature = inspect.signature(function)
        hints = typing.get_type_hints(function)
        alias_of = {alias: name for name, names in aliases.items() for alias in names}

        @functools.wraps(function)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            repairs: list[str] = []
            canonical: dict[str, Any] = {}
            for key, value in kwargs.items():
                if key in refusals:
                    raise TypeError(f"{function.__name__}() does not take {key!r}: {refusals[key]}")
                name = alias_of.get(key, key)
                if name not in signature.parameters:
                    valid = ", ".join(signature.parameters)
                    raise TypeError(f"{function.__name__}() got an unexpected keyword argument {key!r}; valid: {valid}")
                if name in canonical:
                    raise TypeError(f"{function.__name__}() got {name!r} twice (as {key!r})")
                if name != key:
                    repairs.append(f"{key}= read as {name}=")
                canonical[name] = value
            bound = signature.bind(*args, **canonical)
            for name, value in bound.arguments.items():
                bound.arguments[name] = _coerce(name, value, hints.get(name), repairs)
            result = function(*bound.args, **bound.kwargs)
            if repairs:
                result.warnings.extend(f"Repaired argument: {repair}" for repair in repairs)
            return result

        return typing.cast(_F, wrapper)

    return decorate


_PATH_ALIASES = ("file_path", "filepath", "file", "filename", "path_or_file")


@charitable({"path": _PATH_ALIASES, "sel": ("selector", "lines", "range")})
def read(path: str, sel: str | None = None) -> Doc:
    """Read a file or directory (``read@1``).

    ``path`` may carry a selector: ``"src/a.rs:50-120"``, ``":N+K"``,
    ``":raw"``. ``sel`` is the same selector without the colon. A file
    prints as ``[path#TAG]`` plus ``N:TEXT`` rows (first 400 lines unless a
    selector says otherwise); the shown lines become editable anchors.
    """
    target = path if sel is None else f"{path}:{sel}"
    reply = _call("fs.read", {"path": target})
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
    )


@charitable({"path": _PATH_ALIASES, "content": ("text", "contents", "data", "body")})
def write(path: str, content: str) -> WriteResult:
    """Create or overwrite a file atomically (``write@1``).

    Parent directories are created. A replaced file keeps its BOM, line
    endings, and mode. Prefer ``edit`` for changes to an existing file.
    """
    if not isinstance(content, str):
        raise TypeError(f"content must be str, got {type(content).__name__}")
    reply = _call("fs.write", {"path": path, "content": content})
    return WriteResult(
        version=reply["version"],
        path=reply["path"],
        absolute=reply["absolute"],
        created=reply["created"],
        bytes=reply["bytes"],
        tag=reply["tag"],
        made_executable=reply["made_executable"],
        rendered=reply["rendered"],
    )


_EXACT_STRING_HINT = (
    "edit() takes a hashline patch, not old/new strings. read() or grep() the file, then send "
    "'[path#TAG]\\nPUT 12.=14:\\n+new line' with the header and line numbers they printed."
)


@charitable(
    {"patch": ("input", "diff", "edits", "payload")},
    {name: _EXACT_STRING_HINT for name in ("old_str", "new_str", "old_string", "new_string", "old", "new")},
)
def edit(patch: str) -> EditResult:
    """Apply a hashline payload (``edit@hl.1``), the grammar of the ``edit``
    tool: ``[path#TAG]`` sections of ``PUT``/``CUT``/``REM``/``MV`` ops whose
    line numbers come from the latest ``read``/``grep``/edit result.

    For programmatic edits (loops, codemods); raises :class:`EditRejected`.
    """
    if not isinstance(patch, str):
        raise TypeError(f"patch must be str, got {type(patch).__name__}")
    reply = _call("fs.edit", {"input": patch})
    return EditResult(version=reply["version"], rendered=reply["rendered"], files=reply["files"])


@charitable(
    {
        "pattern": ("regex", "query", "pat"),
        "path": _PATH_ALIASES + ("paths", "dir", "directory"),
        "ignore_case": ("i", "case_insensitive", "ignorecase"),
        "context": ("C", "context_lines"),
    }
)
def grep(
    pattern: str,
    path: str = ".",
    *,
    glob: str | None = None,
    ignore_case: bool = False,
    context: int = 0,
    limit: int | None = None,
    skip: int = 0,
) -> Hits:
    """Search files with a Rust regex (``grep@1``), gitignore-aware.

    ``path`` is a file, directory, or glob; ``;`` separates several. Prints
    ``[path#TAG]`` groups of ``*N:TEXT`` (match) and `` N:TEXT`` (context)
    rows; every printed line becomes an ``edit`` anchor. Results page by
    file: pass ``skip`` from the pagination notice.
    """
    reply = _call(
        "fs.grep",
        {
            "pattern": pattern,
            "path": path,
            "glob": glob,
            "ignore_case": ignore_case,
            "context": context,
            "limit": limit,
            "skip": skip,
        },
    )
    hits = [
        Hit(path=file["path"], tag=file["tag"], line=line, text=text)
        for file in reply["files"]
        for line, text in file["matches"]
    ]
    return Hits(hits, reply["version"], reply["rendered"], reply["total_files"], reply["more_files"])


@charitable({"pattern": ("glob", "patterns", "query"), "path": _PATH_ALIASES + ("dir", "directory", "root")})
def glob(pattern: str, path: str = ".", *, hidden: bool = False, limit: int | None = None) -> Paths:
    """List paths matching ``pattern`` under ``path`` (``glob@1``),
    gitignore-aware, newest first. A bare ``*.rs`` matches at any depth; ``;``
    separates several patterns."""
    target = pattern if path in (".", "") else ";".join(f"{path.rstrip('/')}/{part.strip()}" for part in pattern.split(";"))
    reply = _call("fs.glob", {"path": target, "hidden": hidden, "limit": limit})
    return Paths(reply["paths"], reply["version"], reply["rendered"], reply["truncated"])
