# Subagent API (`rlm.*`)

All calls are async unless marked otherwise; `await` works at the top level of the REPL.

## The tree

Each session builds a tree of agents, starting at depth 0. An agent below the depth limit (`rlmMaxDepth`, default 2) can spawn children one level deeper. Children are persistent sessions, like the root. An agent messages and observes only its parent (none at depth 0) and its own children; siblings, grandchildren and other roots are unreachable. Messaging and observation: the `agent-message` and `agent-observe` skills.

## Spawn

- `rlm.spawn(prompt: str, *, name: str, why: str, model: str | None = None, thinking: str | None = None, workspace: str | None = None, budget: dict | None = None, accept: list[dict] | None = None, accept_intent: bool | None = None, accept_returns: int | None = None) -> RLMSpawnHandle`: spawns one child; returns at once.
  - `why`: required; one of `"parallel"` (independent tasks run at once), `"isolate"` (the work would bloat this context; only a compact result comes back), `"tools"` (the task needs a tool set or instructions that conflict with this agent's), `"user"` (the user asked for a subagent). A missing or other value is refused with the rule and the four values.
  - `name`: short, descriptive, unique among the child's siblings.
  - `model`, `thinking`: inherited from the parent when not given.
  - `workspace`: `"shared"` (default) works in the parent's directory; `"isolated"` gives the child a copy-on-write copy of the parent's workspace whose changes come back when it ends (conflicts are reported).
  - `budget`: a budget of the child's own, a dict with any of `cost_usd`, `tokens`, `time_s`, `tool_calls`, `requests`: it leaves this task's budget at the spawn, and what the child did not spend returns when the child ends. Without `budget` the child draws from this task's budget, shared by the whole tree; it can never take the reserve this agent keeps for its final answer. With a budget on this task, a named budget must cover every dimension the task's budget limits (`time_s` left out: what is left before the deadline). A spawn whose budgets do not fit is refused with `Budget: the children's allotments do not fit what is left (<dimension>)` and spawns nothing. `await budget.status()` returns what this task's budget has left (`None` without a budget).
  - `accept`: the child's acceptance checks, set before its first run with you as their owner; the child can read them; only you set them. Each is one of:
    - `{"kind": "command", "command": "pytest -q", "expect": 0, "timeout_ms"?: int, "protect"?: [paths]}`: confirmed when the command exits with `expect` (default 0) and no `protect` file changed.
    - `{"kind": "judge", "condition": str, "evidence"?: [commands], "model"?: str}`: a judge (one model request with no tools and no transcript; the session's model unless `model` names one) decides the condition from the output of the other checks and the `evidence` commands.
    - `{"kind": "until", "command": str, "timeout_ms"?: int}`: a command that exits 0 once the condition holds.
    The child's "done" counts only when the harness confirms every check on its final state; a refuted one goes back to the child with its evidence. The child's report and `rlm.collect` carry the verdict the harness read (`checks passed, unconfined`, `failed` or `unverified`, with `k/n` checks confirmed), never the child's own claim. A bad check, an unknown key or kind, or `accept_intent`/`accept_returns` without `accept` fails the spawn with an error naming the kwarg.
  - `accept_intent`: with `accept`, default `True`: the intent check joins them (a judge decides from the child's task whether its final state meets it). `accept=[]` with the default gives the intent check only.
  - `accept_returns`: the most times in a row a refuted "done" goes back to the child before it ends failed (default 3).
  - The result never arrives as a return value; it arrives as an agent message. To block until it does, pass the handle to `await jobs.wait(handle)` (or call `await jobs.wait()` for the first of all running work); never poll.
  - Refused when the caller is at the depth limit or the family's running-subagent cap (`subagentMaxConcurrency`) is full.
- `rlm.spawn_batch(tasks: list[dict]) -> list[RLMSpawnHandle]`: each dict `{prompt, name, why, model?, thinking?, workspace?, budget?, accept?, accept_intent?, accept_returns?}` as in `rlm.spawn`. All or none admit: a batch that would exceed the cap fails with `subagent concurrency limit N is already full`, one whose allotments do not fit the budget with the budget refusal.
- `rlm.find_models(query: str = "", limit: int = 8) -> list[RLMModel]`: models backed by active credentials; pass `selector` as `model`.

## Query (a sub-model call over data)

- `rlm.query(prompt: str, context: str | None = None, *, model: str | None = None, thinking: str | None = None, max_bytes: int | None = None) -> RLMText`: one model call with no tools, no session and no transcript entry; the answer is a value and enters the conversation only if the cell prints it.
  - `context`: the slice the prompt is about (sent before the prompt, inside `<context>` tags).
  - `model`: an exact `provider/id` (see `rlm.find_models`); default the `rlm.queryModel` setting, else this session's model. `thinking`: a reasoning level; default the model's own.
  - `max_bytes`: cut the answer to at most that many UTF-8 bytes at a character boundary.
  - Raises `rlm.RLMQueryError` when the call fails or the batch is refused.
- `rlm.query_batch(calls: list[dict], *, concurrency: int | None = None) -> list[RLMText | RLMQueryError]`: each dict `{prompt, context?, model?, thinking?, max_bytes?}` as in `rlm.query`; answers in order, a failed call's `RLMQueryError` in its place. A context shared by many calls is sent to the host once.
  - Admission is all or none: over the session's input-byte budget (`rlm.queryBudgetBytes`, 0: none) the batch raises `rlm.query needs N bytes of input; the session's query budget has L of B bytes left (rlm.queryBudgetBytes)`; with every query slot of the session busy (`rlm.queryConcurrency`, default 4) it raises `rlm.query concurrency limit N is already full`.
  - The calls run in waves of at most `concurrency` (default and ceiling: the free query slots), in order.
  - Each call's usage counts into this session's usage.
- `RLMText`: a `str` with `.truncated: bool` (cut by `max_bytes` or the model's output limit) and `.model: str` (`provider/id`).

## The conversation as data

Synchronous reads (no `await`) that return values and print nothing; slice them in code and query the slices.

- Sessions without chat memory:
  - `history.entries(*, kind: str | None = None) -> list[HistoryEntry]`: every entry of this conversation, oldest first, compactions and what they summarized included.
  - `history.entry(id: int) -> HistoryEntry`.
  - `history.compactions() -> list[HistoryEntry]`: each compaction's summary is its `text`; the entries before its `first_kept_id` are what it summarized.
  - `HistoryEntry`: `id`, `kind` (`user`, `assistant`, `tool_result`, `compaction`, `reset`, `system`, `bash`, `custom`, ...), `text`, `tool_calls` (`ToolCall(id, name, arguments)`), `tool_call_id`, `tool_name`, `is_error`, `custom_type`, `first_kept_id`, `timestamp`.
- Chat-memory sessions (read by zoom only; there is no search):
  - `chat.view() -> list[ChatLine]`: the view's lines, `ChatLine(id, n, text)`: the `n` messages from `id` on, summarized.
  - `chat.zoom(id: int, n: int) -> list[ChatLine]`: the two lines line `(id, n)` was built from (`n` > 1).
  - `chat.message(id: int) -> str`: message `id` whole, as `kind: text`.
- Each object raises in the other kind of session, naming the reads that fit.

## Track and collect

- `rlm.list_subagents() -> list[RLMSubagent]`: direct children; rows carry live activity (current activity, tool use count, duration, answer preview, latest progress note). Use after a kernel restart or compaction to get handles back.
- `rlm.collect(targets=None, *, timeout_ms: int = 0) -> list[RLMChildResult]`: typed snapshots of direct children (status, settled flag, answer preview, error, and `acceptance`: the verdict of a child spawned with `accept`) without steering them. `timeout_ms=0`: non-blocking snapshot; a positive timeout (at most 30 minutes) blocks this call until the children settle or the deadline passes.
- `rlm.progress_note(message: str) -> dict`: a child reports brief in-flight progress to its parent (at most 512 characters, about one note per 10 seconds); the parent sees it without a reply.
- `rlm.rename(new_name: str, *, session_id=None) -> str`: renames this session (omit `session_id`) or a direct child (spawn handle, `list_subagents()` row, or session id; never the child's name). Names stay unique among siblings.
- `rlm.delete_subagent(target: str | RLMSubagent | RLMSpawnHandle) -> RLMSubagent`: deletes one direct child. Only when it is idle and its context is no longer needed.

## Types

- `RLMSpawnHandle`: `rlm_child_id: str`, `name: str`, `session_dir: Path`, `model: str` (provider/model).
- `RLMSubagent`: `rlm_child_id: str`, `active_session_id: str | None`, `session_id: str | None`, `session_name: str`, `session_dir: Path`, `status: Literal["running", "completed", "error", "cancelled"]`, plus the live activity fields. `cancelled`: the child's run was stopped before it answered (Esc on the cell that waited on it, or a cancel); the row stays until the child is deleted, and `jobs.list()` shows it as `aborted`.
- `RLMModel`: `provider: str`, `id: str`, `name: str`, `selector: str` (the exact string to spawn the model).

## Patterns

- Repeated child prompts: wrap `rlm.spawn` in a small Python function that fills an f-string template, so each spawn passes the same contract.
- Fan-in through files: tell each child to write its result to a named file and reply with the path; read the files once the replies arrive.
- Many agents with a fixed shape (fan-out, pipeline, review loop): the `workflow` tool ([workflow.md](workflow.md)), or the `factory` skill for stored state machines.
