---
name: rlm-heartbeat
description: Create and manage your own recurring wake-ups (agent-owned heartbeats) that re-prompt this session on a schedule with a stored instruction - to check a long build, watch progress or keep coordinating long work. Use when the user asks you to start, schedule or manage a heartbeat, unless they name the user's /heartbeat command, which this skill cannot touch.
---

# RLM Heartbeat

## Steps

1. Check for an existing one first: `await rlm_heartbeat.list()`. Update it rather than stacking duplicates.
2. Write the instruction so a cold turn can act on it: what to inspect, what counts as done, what to do then. "check test progress" is weak; "read build.log; when it shows PASS or FAIL, report it and delete heartbeat 'tests'" is strong.
3. Create: `await rlm_heartbeat.create(instruction, interval="10m", label="tests")`. The default interval is 5 minutes; label each one when several run.
4. Pick the delivery mode: `"steer"` (default) interrupts a busy turn; `"follow_up"` waits for the turn to end. Use `follow_up` unless the check is urgent.
5. Stop it when the work ends: `await rlm_heartbeat.delete(id)`, or pause with `update(id, status="pause")`.

## Rules

- Only for agent-internal recurring checks. A request about `/heartbeat` is the user's own surface: tell the user to use `/heartbeat`.
- Do not use a heartbeat to wait for a child or a `bash()` command: their ends already arrive as messages.

Signatures: [references/api.md](references/api.md).
