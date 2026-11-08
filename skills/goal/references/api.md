# goal API

- `goal.get() -> dict`: `goal` (`None` when no goal is set), `remaining_tokens`, `completion_budget_report`. The `goal` dict: `objective`, `status`, `token_budget`, `tokens_used`, `time_used_seconds`, timestamps. Only one goal is active at a time.
- `goal.create(objective: str, token_budget: int | None = None) -> dict`: starts a new active goal and returns the goal state. Refused while a goal is active, paused or budget-limited.
- `goal.complete() -> dict`: marks the goal achieved and returns the final state, with `completion_budget_report` when a budget was set.
- `goal.remind(text: str) -> dict`: puts a reminder on the Director stack; its text leads the next goal or autonomous continuation and waits on the stack until one comes.
- `goal.force_tool(tool: str, tries: int = 1) -> dict`: forces the next requests to call `tool` until a response calls it; after `1 + tries` requests without the call the run fails and the forced call leaves the stack.
