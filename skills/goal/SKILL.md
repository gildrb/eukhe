---
name: goal
description: Manage the persistent thread goal the harness keeps you working on across turns - read its status and token budget, start one when the user explicitly asks for a long-running goal, mark it complete once its objective is fully achieved, leave a reminder for the next continuation, or force the next request to call a tool.
---

# Goal

## Start

- Create a goal only when the user (or system or developer instructions) asks for a persistent goal: `await goal.create("ship the release notes")`. Never infer one from an ordinary task.
- Pass `token_budget` only when the user names a budget.
- A pending goal (active, paused, budget-limited) refuses `create`; the error says what the user can do. A completed or failed goal is replaced.

## Work

- `await goal.get()` shows the objective, status, usage and remaining tokens.
- `await goal.remind(text)`: text that leads the next continuation (a note to your future self).
- `await goal.force_tool(tool, tries=1)`: the next requests must call `tool`; after `1 + tries` misses the run fails.

## Finish

1. Check that the objective is achieved and no required work remains.
2. `await goal.complete()`. Saying "done" is not enough: the harness continues the goal until this call.
3. If the result has a `completion_budget_report`, report that usage to the user.

Never complete a goal because the budget is low or you are stopping. Pause, resume and clear belong to the user and the host.

Return shapes: [references/api.md](references/api.md).
