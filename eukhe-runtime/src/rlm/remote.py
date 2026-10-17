"""``@remote``: a kernel function the host offers as a tool.

The decorator records the function and announces it to the host
(``remote.register``): its tool name, its JSON schema (from the type hints)
and its docstring. The host reaches it through the ``dyn`` tool as
``remote/<name>`` and calls it with a ``call`` request; the JSON return value
is the tool's result.

    from rlm import remote

    @remote
    def word_count(text: str, unique: bool = False) -> int:
        "Count the words of a text."
        words = text.split()
        return len(set(words)) if unique else len(words)

The host bounds each call by the session's blocking budget. A synchronous
function runs on its own daemon thread, so one that hangs costs that thread,
never the kernel: the call answers a timeout error and the kernel keeps
serving.
"""

from __future__ import annotations

import inspect
import re
import types
import typing
from typing import Any, Callable, TypeVar

__all__ = ["remote", "lookup"]

_F = TypeVar("_F", bound=Callable[..., Any])

_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.-]{0,63}")

# (module, qualname) -> function: what a `call` request resolves.
_registry: dict[tuple[str, str], Callable[..., Any]] = {}


def _schema(annotation: Any) -> dict[str, Any]:
    """The JSON schema of one parameter's type hint; ``{}`` accepts any value."""
    if annotation is inspect.Parameter.empty or annotation is Any:
        return {}
    origin = typing.get_origin(annotation)
    args = typing.get_args(annotation)
    if origin in (typing.Union, types.UnionType):
        options = [_schema(arg) for arg in args if arg is not type(None)]
        schema = options[0] if len(options) == 1 else {"anyOf": options}
        return {"anyOf": [schema, {"type": "null"}]} if type(None) in args else schema
    if origin is typing.Literal:
        return {"enum": list(args)}
    if annotation is bool:
        return {"type": "boolean"}
    if annotation is int:
        return {"type": "integer"}
    if annotation is float:
        return {"type": "number"}
    if annotation is str:
        return {"type": "string"}
    if annotation in (list, tuple, set, frozenset) or origin in (list, tuple, set, frozenset):
        return {"type": "array", "items": _schema(args[0])} if args else {"type": "array"}
    if annotation is dict or origin is dict:
        return {"type": "object"}
    return {}


def _parameters(function: Callable[..., Any]) -> dict[str, Any]:
    """The object schema of the function's keyword arguments."""
    hints = typing.get_type_hints(function)
    properties: dict[str, Any] = {}
    required: list[str] = []
    extra = False
    for name, parameter in inspect.signature(function).parameters.items():
        if parameter.kind in (parameter.POSITIONAL_ONLY, parameter.VAR_POSITIONAL):
            raise TypeError(f"@remote {function.__qualname__}: parameter {name!r} cannot be passed by keyword")
        if parameter.kind is parameter.VAR_KEYWORD:
            extra = True
            continue
        properties[name] = _schema(hints.get(name, inspect.Parameter.empty))
        if parameter.default is inspect.Parameter.empty:
            required.append(name)
    schema: dict[str, Any] = {"type": "object", "properties": properties, "additionalProperties": extra}
    if required:
        schema["required"] = required
    return schema


def remote(function: _F | None = None, /, *, name: str | None = None) -> Any:
    """Offer ``function`` to the host as the tool ``remote/<name>``.

    ``name`` defaults to the function's name. Use bare (``@remote``) or with
    a name (``@remote(name="count")``). Raises ``TypeError`` for a parameter
    that cannot be passed by keyword, ``ValueError`` for a bad name, and the
    host's error when the session refuses the registration.
    """

    def register(target: _F) -> _F:
        if not callable(target):
            raise TypeError("@remote decorates a function")
        tool = name or target.__name__
        if not _NAME.fullmatch(tool):
            raise ValueError(f"@remote name {tool!r} must match {_NAME.pattern}")
        spec = {
            "name": tool,
            "module": target.__module__,
            "function": target.__qualname__,
            "description": inspect.getdoc(target) or "",
            "parameters": _parameters(target),
        }
        _registry[(target.__module__, target.__qualname__)] = target
        from . import host_request_sync, repl

        if repl.is_active():
            host_request_sync("remote.register", spec)
        return target

    if function is None:
        return register
    return register(function)


def lookup(module: str, function: str) -> Callable[..., Any] | None:
    """The ``@remote`` function registered as ``function`` of ``module``."""
    return _registry.get((module, function))
