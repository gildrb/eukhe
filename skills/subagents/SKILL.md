---
name: subagents
description: Decide whether a subagent is justified, then spawn, brief and collect it. Read before any rlm.spawn or rlm.spawn_batch call - when a task splits into independent parts that can run at once, when work would flood this context with material of which only a summary matters, when a task needs tools or instructions that conflict with yours, or when the user asks for a subagent. Covers the required why value, dividing work by context, self-contained prompts, compact hand-back and fan-in, and when rlm.query (a tool-less sub-model call over a slice of data) does the job instead.
---

# Subagents

Default: do the work in this loop. A child costs a fresh context, a full briefing and a hand-back. It pays only when this loop would get worse without it.

## Decide

| `why` | Spawn when | Not when |
|---|---|---|
| `parallel` | independent tasks can run at once, each in a fresh context you can discard | the tasks share state or must run in order |
| `isolate` | the work reads far more than it returns (a broad search, long logs, a large diff) and only a compact result matters | one known lookup, edit or command |
| `tools` | the task needs a tool set or instructions that conflict with yours | you only lack know-how: read the matching skill |
| `user` | the user asked for a subagent | |

No row fits: do it here.

## Query instead

A function over a slice, no tools: `await rlm.query(prompt, context)`, or `rlm.query_batch([...])` for many. No child, briefing or transcript: the answer is a Python value; print only what you need. Keep long material (files, logs, this conversation through `history` or `chat`) in variables, slice it in code, query each slice, combine the values. Spawn only when the work needs tools, its own loop or a hand-back.

## Spawn

1. Divide by context, not by role: one child per independent body of material (a directory, a dataset, a question). Never chain planner, coder and reviewer children over the same material.
2. Brief fully: goal, exact paths and facts, constraints, what done means. A child never sees this conversation.
3. Ask for a compact hand-back: the answer, decisions and paths, not transcripts. Bulky output goes to a file; the reply names it.
4. Pass `why` and a short unique `name`; keep the handle. Children that edit one tree in parallel get `workspace="isolated"`.
5. Several children: one `rlm.spawn_batch` call.

## Collect

- Results arrive as agent messages, never as return values. Do other work meanwhile; when only their results remain, `await jobs.wait()` in this turn. Never poll; never end the turn while children run.
- `rlm.collect()` snapshots children without steering them. Read the files they wrote.
- After a kernel restart or compaction, `rlm.list_subagents()` returns the handles.
- Delete a child only when it is idle and its context is no longer needed.

## Refusals

A refused spawn (depth limit, concurrency cap, missing or wrong `why`) states its rule. Act on it: do the work here, wait for a running child to settle, or fix `why`. Never retry unchanged.

Signatures and types: [references/api.md](references/api.md).
