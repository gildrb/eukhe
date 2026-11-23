---
name: factory
description: Run a stored state machine of child agents (a factory) - fan-out, bounded review-and-fix loops, joins, one child per list item - that keeps running in the background after your turn. Use when the user asks for a factory or a machine (builder, pr-manager, review-sweep), or when a multi-agent workflow must be saved, rerun, paused and resumed. Off by default; the user enables it with /factory on.
---

# Factory

A factory entry is a validated machine: states, each backed by a subagent spec, joined by guarded transitions. A run spawns each state's child, feeds captured outputs into the next prompts, and runs to quiescence in a background kernel task. A state without `scope` is read-only; a writing state names its files (`"scope": ["docs/{topic}.md"]`), and its instances start together as one batch of the agent tree.

## Choose

| Need | Use |
|---|---|
| a one-off fan-out or pipeline for this request | the `workflow` tool |
| a few independent children now | the subagents skill |
| a saved shape to rerun, pause, resume and watch | a factory |

## Steps

1. Read the guide first: `print(rlm.factory.help())`. It covers states, ports, guards, joins, foreach, residents, budgets and the run calls, with examples. It answers even while the factory is off.
2. Reuse before you write: the library holds bundled machines (`builder`, `pr-manager`, `review-sweep`) and the user's own; `eukhe factory list` shows them.
3. Store the spec: `rlm.harness.create_factory(...)` with exactly one of a machine form or `dag` sugar. An invalid spec is refused with the reason and never stored; fix it and retry.
4. Start: `await rlm.factory.run("<spec_id>")` returns at once with the run id; the run goes on in the background.
5. Follow it to its end: do other work, then `rlm.factory.watch(run_id, timeout)` or `rlm.factory.status(run_id)`. A paused run (a failed state under `escalate`, a run budget) waits on you, not the user: read its status, then `resume`, change the spec and rerun, or `stop`; report the outcome in your final answer.

## Refusals

- `the factory is disabled; run /factory on to enable it`: `/factory on` is the user's setting. Do the same work with the `workflow` tool or the subagents skill, and name `/factory on` in your final answer.
- `/factory off` is refused while runs are live, so a running factory keeps its stop path.

Library, TUI page and settings: [references/guide.md](references/guide.md).
