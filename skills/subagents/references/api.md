# Subagent API (`rlm.*`)

All calls are async unless marked otherwise; `await` works at the top level of the REPL.

## The family

Each session builds a tree of agents, starting at depth 0. An agent below the depth limit (`rlmMaxDepth`, default 2) can spawn children one level deeper. Children are persistent sessions, like the root. The family is every agent under one root session: the parent (none at depth 0), siblings (same parent), children, and relatives (every other agent in the tree). Root sessions are each other's siblings; another root's subagents are outside the family. Messaging and observation: the `agent-message` and `agent-observe` skills.

## Spawn

- `rlm.spawn(prompt: str, *, name: str, why: str, model: str | None = None, thinking: str | None = None, workspace: str | None = None) -> RLMSpawnHandle`: spawns one child; returns at once.
  - `why`: required; one of `"parallel"` (independent tasks run at once), `"isolate"` (the work would bloat this context; only a compact result comes back), `"tools"` (the task needs a tool set or instructions that conflict with this agent's), `"user"` (the user asked for a subagent). A missing or other value is refused with the rule and the four values.
  - `name`: short, descriptive, unique among the child's siblings.
  - `model`, `thinking`: inherited from the parent when not given.
  - `workspace`: `"shared"` (default) works in the parent's directory; `"isolated"` gives the child a copy-on-write copy of the parent's workspace whose changes come back when it ends (conflicts are reported).
  - The result never arrives as a return value; it arrives as an agent message.
  - Refused when the caller is at the depth limit or the family's running-subagent cap (`subagentMaxConcurrency`) is full.
- `rlm.spawn_batch(tasks: list[dict]) -> list[RLMSpawnHandle]`: each dict `{prompt, name, why, model?, thinking?, workspace?}` as in `rlm.spawn`. All or none admit: a batch that would exceed the cap fails with `subagent concurrency limit N is already full`.
- `rlm.create_session(prompt: str, name: str | None = None, model: str | None = None, thinking: str | None = None, cwd: str | None = None) -> RLMCreateSessionHandle`: creates another depth-0 session (a sibling root, not a child). Only at depth 0 with a daemon; returns after the session exists and its first prompt is sent.
- `rlm.find_models(query: str = "", limit: int = 8) -> list[RLMModel]`: models backed by active credentials; pass `selector` as `model`.

## Track and collect

- `rlm.list_subagents() -> list[RLMSubagent]`: direct children; rows carry live activity (current activity, tool use count, duration, answer preview, latest progress note). Use after a kernel restart or compaction to get handles back.
- `rlm.collect(targets=None, *, timeout_ms: int = 0) -> list[RLMChildResult]`: typed snapshots of direct children (status, settled flag, answer preview, error) without steering them. `timeout_ms=0`: non-blocking snapshot; a positive timeout, clamped to the blocking budget, blocks this call until the children settle or the deadline passes.
- `rlm.progress_note(message: str) -> dict`: a child reports brief in-flight progress to its parent (at most 512 characters, about one note per 10 seconds); the parent sees it without a reply.
- `rlm.rename(new_name: str, *, session_id=None) -> str`: renames this session (omit `session_id`) or a direct child (spawn handle, `list_subagents()` row, or session id; never the child's name). Names stay unique among siblings.
- `rlm.delete_subagent(target: str | RLMSubagent | RLMSpawnHandle) -> RLMSubagent`: deletes one direct child. Only when it is idle and its context is no longer needed.

## Types

- `RLMSpawnHandle`: `rlm_child_id: str`, `name: str`, `session_dir: Path`, `model: str` (provider/model).
- `RLMCreateSessionHandle`: `active_session_id: str` (live daemon instance), `session_id: str` (durable identity), `name: str`, `session_file: Path`, `model: str`.
- `RLMSubagent`: `rlm_child_id: str`, `active_session_id: str | None`, `session_id: str | None`, `session_name: str`, `session_dir: Path`, `status: Literal["running", "completed", "error"]`, plus the live activity fields.
- `RLMModel`: `provider: str`, `id: str`, `name: str`, `selector: str` (the exact string to spawn the model).

## Patterns

- Repeated child prompts: wrap `rlm.spawn` in a small Python function that fills an f-string template, so each spawn passes the same contract.
- Fan-in through files: tell each child to write its result to a named file and reply with the path; read the files once the replies arrive.
- Many agents with a fixed shape (fan-out, pipeline, review loop): the `workflow` tool, or the `factory` skill for stored state machines.
