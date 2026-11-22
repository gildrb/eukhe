---
name: directors
description: Steer the harness's autonomous run (/auto) from the REPL - leave a reminder that leads the next continuation, force the next requests to call a tool, or read the task's acceptance checks and their last verdicts before you call the work done.
---

# Directors

The user starts and stops an autonomous run with `/auto`; while it runs, the harness continues you until the task is done, its checks pass, the budget runs out, or the run stops making progress. This skill puts Directors on that run's stack and reads its checks. It never starts, pauses or ends the run.

## Steer

- `await directors.remind(text)`: text that leads the next continuation (a note to your future self: the next step, a constraint, what to verify). It waits on the stack until a continuation comes.
- `await directors.force_tool(tool, tries=1)`: the next requests must call `tool`; after `1 + tries` misses the run fails. Use it only when a step must go through that tool.

## Checks

- `await directors.acceptance()` shows the task's acceptance checks and their last verdicts. Only the task's owner sets them.
- Read them before you say the work is done: the harness judges the final state against every check, and a failed check comes back as your next input with its evidence. Fix the work; never argue with the verdict.

## Progress

Each continuation must take a concrete step with a new result. Continuations without one count as stalls: at `directors.stallSteps` in a row the harness asks you once to change approach; at twice that the run ends, not done. Change method, investigate with a read-only helper, or re-plan instead of repeating the same call.

Return shapes: [references/api.md](references/api.md).
