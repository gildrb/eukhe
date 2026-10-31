---
name: refine
description: Ask for a continual-harness refinement from the REPL after you observe a repeated failure, a reusable tactic, a repeated delegation role or a behavior policy worth keeping across sessions. A second model reads the transcript and applies a small, evidence-backed update (a skill or subagent spec, and in harness-memory sessions a memory or prompt note). Returns at once; it runs when the turn ends.
---

# Refine

## When

- The same failure happened twice, or a tactic worked that the next session should reuse.
- You spawned the same kind of child more than once (a subagent spec), or followed the same multi-step procedure more than once (a skill).
- Not for one-off facts, and not to rewrite the whole harness when one focused entry is enough.

## How

1. `await refine.run("turn the release checklist into a skill")`. The text points the refinement at one observation; it is optional.
2. `global_=True` writes to the global store (every session); the default is this session's store.
3. Keep working. The refinement runs when the turn ends, rebuilds the system prompt and resumes you with a harness message that lists the applied edits.

## Rules

- `await refine.status()` shows `pending` (queued this turn) and `in_flight` (planning or applying).
- One request per turn; a second `run` only replaces the instructions.
- `{"scheduled": False, "reason": ...}`: it cannot start now (no active turn); do not retry in a loop. Refinement runs only in a top-level session; elsewhere the call fails with an error.
