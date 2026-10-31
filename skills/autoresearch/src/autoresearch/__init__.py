"""Eukhe autoresearch skill: an autonomous experiment loop from the kernel.

Every decision (which runs count, whether a keep is an improvement, the
baseline, the best result, the confidence, the iteration cap) is the host's
compiled Lab; these functions are typed wrappers over the host bridge
(`rlm.host_request`) that format its replies. Metric values are exact
decimal strings. They only work inside the Eukhe Python kernel.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from decimal import Decimal, InvalidOperation
from typing import Any

from rlm import host_request

_STATUSES = ("keep", "discard", "crash", "checks_failed")
_DIRECTIONS = ("lower", "higher")


def _strings(name: str, values: Iterable[str]) -> list[str]:
    if isinstance(values, str):
        raise TypeError(f"{name} must be a list of strings, not a string")
    out = list(values)
    for value in out:
        if not isinstance(value, str):
            raise TypeError(f"{name} must hold strings, got {type(value).__name__}")
    return out


def _text(name: str, value: Any, *, optional: bool = False) -> None:
    if value is None and optional:
        return
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str, got {type(value).__name__}")


def _decimal(value: str | None) -> Decimal | None:
    if value is None:
        return None
    try:
        return Decimal(value)
    except InvalidOperation:
        return None


def _delta(value: str | None, base: str | None) -> str | None:
    """`value` against `base` in percent, signed, one decimal."""
    current, reference = _decimal(value), _decimal(base)
    if current is None or reference is None or reference == 0:
        return None
    return f"{(current - reference) / abs(reference) * 100:+.1f}%"


def _confidence(tenths: int | None) -> str | None:
    if tenths is None:
        return None
    if tenths >= 20:
        verdict = "likely real"
    elif tenths >= 10:
        verdict = "marginal"
    else:
        verdict = "within noise"
    return f"{tenths // 10}.{tenths % 10}x noise floor ({verdict})"


def _progress(state: Mapping[str, Any]) -> str:
    config = state.get("config") or {}
    cap = config.get("max_iterations")
    logged = state.get("logged", 0)
    return f"{logged}/{cap}" if cap is not None else str(logged)


def _row(row: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if row is None:
        return None
    out = dict(row)
    out["metrics"] = {name: value for name, value in row.get("metrics", [])}
    return out


def _state(state: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "mode": state["mode"],
        "config": state["config"],
        "segment": state["segment"],
        "pending": state["pending"],
        "baseline": state["baseline"],
        "best": state["best"],
        "best_vs_baseline": _delta(state["best"], state["baseline"]),
        "confidence": _confidence(state["confidence_tenths"]),
        "progress": _progress(state),
        "runs": [_row(row) for row in state["runs"]],
        "runs_in_segment": state["runs_in_segment"],
    }


def _flag(entry: Any) -> dict[str, Any]:
    if isinstance(entry, Mapping):
        run, reason = entry.get("run"), entry.get("reason")
    elif isinstance(entry, (tuple, list)) and len(entry) == 2:
        run, reason = entry
    else:
        raise TypeError("each flag_runs entry must be {'run': n, 'reason': text} or (n, text)")
    if not isinstance(run, int) or isinstance(run, bool):
        raise TypeError(f"flag run must be int, got {type(run).__name__}")
    _text("flag reason", reason)
    return {"run": run, "reason": reason}


async def init(
    name: str,
    metric: str,
    *,
    goal: str | None = None,
    unit: str = "",
    direction: str = "lower",
    secondary: Iterable[str] = (),
    scope: Iterable[str] = (),
    off_limits: Iterable[str] = (),
    constraints: Iterable[str] = (),
    max_iterations: int | None = None,
    new_segment: bool = False,
) -> dict[str, Any]:
    """Open or reconfigure the session on this branch and turn the loop on.

    `metric` is the name the harness prints as `METRIC <name>=<value>`;
    `direction` is "lower" or "higher" (which is better). Off an
    `autoresearch/*` branch it creates one (the tree must be clean); on it,
    the harness changes are committed as the baseline. Pass
    `new_segment=True` to start a fresh baseline (after an intended
    change of `autoresearch.sh`, the metric or the direction).
    """
    _text("name", name)
    _text("metric", metric)
    _text("goal", goal, optional=True)
    _text("unit", unit)
    if direction not in _DIRECTIONS:
        raise ValueError(f"direction must be 'lower' or 'higher', got {direction!r}")
    if max_iterations is not None and (
        not isinstance(max_iterations, int) or isinstance(max_iterations, bool)
    ):
        raise TypeError(f"max_iterations must be int or None, got {type(max_iterations).__name__}")
    payload: dict[str, Any] = {
        "name": name,
        "metric": metric,
        "goal": goal,
        "unit": unit,
        "direction": direction,
        "secondary": _strings("secondary", secondary),
        "scope": _strings("scope", scope),
        "off_limits": _strings("off_limits", off_limits),
        "constraints": _strings("constraints", constraints),
        "max_iterations": max_iterations,
        "new_segment": bool(new_segment),
    }
    reply = await host_request("autoresearch.init", payload)
    return {"branch": reply["branch"], "git": reply["git"], **_state(reply["state"])}


async def run(timeout_s: float = 600) -> dict[str, Any]:
    """Run the benchmark (`bash autoresearch.sh` in the repository root) once.

    The command is fixed. Returns whether it passed (exit 0, no timeout),
    the exit code, the parsed metrics, the last lines of its output (at
    most 10 lines, 4 KB), the full log path, and the baseline and best of
    the segment. A run must be logged before the next one.
    """
    if not isinstance(timeout_s, (int, float)) or isinstance(timeout_s, bool) or timeout_s <= 0:
        raise ValueError("timeout_s must be a positive number")
    reply = await host_request("autoresearch.run", {"timeout_s": timeout_s})
    row = _row(reply["run"]) or {}
    config = reply["config"] or {}
    return {
        "run": row.get("id"),
        "passed": row.get("passed", False),
        "exit_code": reply["exit_code"],
        "timed_out": reply["timed_out"],
        "refused": reply["refused"],
        "metric": {config.get("metric"): row.get("metric")},
        "metrics": row.get("metrics", {}),
        "vs_baseline": _delta(row.get("metric"), reply["baseline"]),
        "vs_best": _delta(row.get("metric"), reply["best"]),
        "baseline": reply["baseline"],
        "best": reply["best"],
        "tail": reply["tail"],
        "log": reply["log"],
    }


async def log(
    status: str,
    description: str,
    *,
    justification: str | None = None,
    flag_runs: Iterable[Any] = (),
) -> dict[str, Any]:
    """Log the pending run: "keep", "discard", "crash" or "checks_failed".

    `keep` commits the run's changes and needs a passed run whose metric
    beats the best kept one (the first keep is the baseline); the host
    refuses any other keep and says why. Every other status resets the tree
    to the last commit. `crash` is for a run that did not pass,
    `checks_failed` for one that passed but failed your checks. A keep that
    changed paths outside the scope (or inside off_limits) needs a
    `justification`. `flag_runs` (`{"run": n, "reason": text}` items) first
    marks earlier runs as suspect: they leave baseline, best and confidence.
    """
    if status not in _STATUSES:
        raise ValueError(f"status must be one of {', '.join(_STATUSES)}; got {status!r}")
    _text("description", description)
    _text("justification", justification, optional=True)
    flags = [_flag(entry) for entry in flag_runs]
    reply = await host_request(
        "autoresearch.log",
        {
            "status": status,
            "description": description,
            "justification": justification,
            "flag_runs": flags,
        },
    )
    state = reply["state"]
    row = _row(reply["run"]) or {}
    return {
        "run": row,
        "vs_baseline": _delta(row.get("metric"), state["baseline"]),
        "baseline": state["baseline"],
        "best": state["best"],
        "confidence": _confidence(state["confidence_tenths"]),
        "git": reply["git"],
        "deviations": reply["deviations"],
        "flagged": reply["flagged"],
        "progress": _progress(state),
        "stopped": reply["stopped"],
        "mode": state["mode"],
    }


async def flag(run: int, reason: str) -> dict[str, Any]:
    """Mark run `run` as suspect (e.g. reward-hacked); it leaves baseline, best and confidence."""
    flags = _flag({"run": run, "reason": reason})
    reply = await host_request("autoresearch.flag", flags)
    return _state(reply["state"])


async def notes(body: str | None = None, idea: str | None = None) -> str:
    """Read the session notes; `body` replaces them, `idea` adds a bullet under `## Ideas`."""
    _text("body", body, optional=True)
    _text("idea", idea, optional=True)
    reply = await host_request("autoresearch.notes", {"body": body, "idea": idea})
    return reply["notes"]


async def state() -> dict[str, Any]:
    """The session of this branch: mode, config, runs, baseline, best, confidence, pending run, notes."""
    reply = await host_request("autoresearch.state")
    return {
        "root": reply["root"],
        "branch": reply["branch"],
        "harness": reply["harness"],
        "store": reply["store"],
        "notes": reply["notes"],
        **_state(reply["state"]),
    }
