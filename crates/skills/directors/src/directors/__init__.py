"""Eukhe directors skill: steer the autonomous run from the kernel.

The Director stack and the acceptance checks live in the host; these
functions are thin typed wrappers over the generic host bridge
(`rlm.host_request`). They only work inside the Eukhe Python kernel.
"""

from __future__ import annotations

from typing import Any

from rlm import host_request


async def remind(text: str) -> dict[str, Any]:
    """Put a reminder on the Director stack.

    Its text leads the next autonomous continuation. While no continuation
    comes, the reminder waits on the stack. Returns the Director stack
    (`stack`, bottom first).
    """
    if not isinstance(text, str):
        raise TypeError(f"text must be str, got {type(text).__name__}")
    return await host_request("directors.push", {"layer": "reminder", "text": text})


async def force_tool(tool: str, tries: int = 1) -> dict[str, Any]:
    """Force the next requests to call `tool` until a response calls it.

    A forced run asks up to `1 + tries` times. When no response calls the
    tool, the run fails and the forced call leaves the stack. Returns the
    Director stack (`stack`, bottom first).
    """
    if not isinstance(tool, str):
        raise TypeError(f"tool must be str, got {type(tool).__name__}")
    if not isinstance(tries, int):
        raise TypeError(f"tries must be int, got {type(tries).__name__}")
    return await host_request(
        "directors.push", {"layer": "forceTool", "tool": tool, "tries": tries}
    )


async def acceptance() -> dict[str, Any]:
    """Read the acceptance checks of this task and their last verdicts.

    Returns a dict with `label` (`checks_passed_unconfined`,
    `checks_passed_not_certified`, `failed` or `unverified`), `checks` (each
    with its `spec` and, once judged, its `result`: `verdict`, `summary`,
    `evidence`; once measured, its `strength`: `caught`, `ran`, `planned`,
    `survivors`), `attacks` (the blind attacks on the checks: `outcome`
    `survived`, `clean` or `unrun`, `path`, `witness`, `required`, `got`,
    `note`), `claimed`, `tries` and `maxReturns`.
    `checks_passed_not_certified`: the checks passed but none was shown to
    catch deliberate breaks of the changed code, or a blind attack's wrong
    code passed them too, so the task is not done.
    Only the task's owner sets the checks.
    """
    return await host_request("acceptance.get")
