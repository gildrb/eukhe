# goal API

- `goal.get() -> dict`: `goal` (`None` when no goal is set), `remaining_tokens`, `completion_budget_report`. The `goal` dict: `objective`, `status`, `token_budget`, `tokens_used`, `time_used_seconds`, timestamps. Only one goal is active at a time.
- `goal.create(objective: str, token_budget: int | None = None) -> dict`: starts a new active goal and returns the goal state. Refused while a goal is active, paused or budget-limited.
- `goal.complete() -> dict`: claims the goal achieved. Without acceptance checks it completes the goal and returns the final state, with `completion_budget_report` when a budget was set. With checks it returns the still active goal and `acceptance` (`status` `pending`, `checks`, `message`): the harness verifies when the turn ends.
- `goal.acceptance() -> dict`: the task's acceptance: `label` (`verified`, `failed`, `unverified`), `checks` (each `spec`, and once judged `result` with `verdict`, `summary`, `evidence`), `claimed`, `tries`, `maxReturns`. Read-only: the task's owner sets the checks.
- `goal.remind(text: str) -> dict`: puts a reminder on the Director stack; its text leads the next goal or autonomous continuation and waits on the stack until one comes.
- `goal.force_tool(tool: str, tries: int = 1) -> dict`: forces the next requests to call `tool` until a response calls it; after `1 + tries` requests without the call the run fails and the forced call leaves the stack.
