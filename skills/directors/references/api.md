# directors API

- `directors.remind(text: str) -> dict`: puts a reminder on the Director stack; its text leads the next autonomous continuation and waits on the stack until one comes. Returns the Director stack (`stack`, bottom first).
- `directors.force_tool(tool: str, tries: int = 1) -> dict`: forces the next requests to call `tool` until a response calls it; after `1 + tries` requests without the call the run fails and the forced call leaves the stack. Returns the Director stack (`stack`, bottom first).
- `directors.acceptance() -> dict`: the task's acceptance: `label` (`checks_passed_unconfined`, `failed`, `unverified`), `state`, `revision`, `checks` (each `spec`, and once judged `result` with `verdict`, `summary`, `evidence`), `claimed`, `tries`, `maxReturns`, and `lastEnd` once a claim ended. Read-only: the task's owner sets the checks.
