---
name: subagents
description: Split work into scoped children or ask read-only helpers, then integrate. Read before the first rlm.split or rlm.spawn; covers when rlm.query suffices.
---

# Subagents

Every agent is a node of one tree. A node does its work alone, or splits into exactly two children with disjoint file scopes and becomes their parent. Read-only helpers are extra leaves. Default: do the work in this loop.

## Decide

| Call | When | Not when |
|---|---|---|
| `rlm.split(left, right)` | two halves write disjoint files, each worth its own planning (several edits or files) | the halves edit the same files; one half needs the other's result |
| `rlm.spawn(task)` | a read-only job: a broad search, long logs, a review; only a compact result matters | one known lookup or command |
| `rlm.query(prompt, context)` | a function over a slice of data, no tools | |

## Split

1. Scope each half by files or directories: `left={"scope": ["crates/a"], "task": "..."}`. A child writes only inside its scope; the rest of your scope stays yours (`own`).
2. Keep shared files (lockfiles, `mod.rs`, index files, generated code) in your own scope. A child that needs one reports a conflict.
3. Brief fully: goal, exact paths and facts, constraints, the check that means done. A child never sees this conversation. A list of work items goes in `items` (their ids): the child accounts for each, and one with items left hands back `stopped` with the list.
4. Each child works in a copy of your workspace as it is now (uncommitted edits included), runs its check there, and reports.
5. While the children run, work on your own scope. A child splits again inside its scope the same way (at most depth 3, 15 agents).

## Integrate

- The harness applies each child's writes inside its scope to your workspace when the child settles. Writes outside its scope are conflicts: never applied; the report lists them, the child's version stays under the workspace's `conflicts/`. Resolve them in your own scope.
- Results arrive as agent messages. When only their results remain, `await jobs.wait()`; a user message ends the wait first. Never poll; never end the turn while children run.
- After each result: run the check, then report.
- A failed child runs once more on its own; a second failure reaches you with its partial work. Absorb it (do that scope yourself) or leave it.

## Refusals

A refused split states its rule (scopes overlap or leave a gap, a half is empty, depth or node bound, budget). Act on it: fix the scopes, do the work here, or wait. Never retry unchanged.

Signatures and types: [references/api.md](references/api.md).
