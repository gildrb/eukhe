---
name: compact
description: Check context usage and compact the conversation from the REPL. Use when context is filling up while substantial work remains, so a dense summary replaces old history and you keep working instead of turning terse or stopping early.
---

# Compact

## When

- Usage is high and real work remains: compact at a natural boundary (a finished step), not mid-thought.
- Unsure: `await compact.status()` gives `tokens`, `context_window`, `percent` (`None` right after a compaction until the next response) and `scheduled`.
- Never as a reason to end the turn or shorten answers.

## How

1. `await compact.run("keep the failing test names and the migration checklist")`. The text tells the summary what the remaining work needs; it is optional.
2. The result is `{"scheduled": True}`, or `{"scheduled": False, "reason": ...}` when there is nothing to compact yet.
3. Keep working. Compaction runs when the turn ends; the harness resumes you with the summary and the recent messages.

## Rules

- One request per turn; a second `run` only replaces the instructions.
- REPL variables, imports and helpers survive compaction.
