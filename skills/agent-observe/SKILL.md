---
name: agent-observe
description: Read-only roster and observation of every agent in your family (everything under your root session). Use to discover reachable agents, see what each is on via its one-line note, and inspect status and bounded recent-message previews without mutating sessions.
---

# Agent Observe

Observe the current agent's family through the local daemon: every agent under
your root session (parent, siblings, children, and `relative`s such as
grandparents, cousins, and grandchildren) plus yourself. Root sessions also
list the other roots as siblings, never their subagents. `list_agents` is the
one family roster and covers every member `agent_message.send` can reach.
`get_agent` and `recent_messages` hydrate an inactive child before reading it.
They cannot read a root sibling that has no live session in this worker.
This skill is read-only: it can list family sessions, inspect one session, and fetch
bounded recent message previews. It cannot prompt, steer, clear, kill, rename, or
otherwise mutate another session.

Call directly from the kernel:

```python
roster = await agent_observe.list_agents()
for agent in roster["agents"]:
    print(agent["relationship"], agent.get("sessionName"), agent["status"], agent.get("note"))
# Ask the specialist whose note shows it already has the context:
await agent_message.send("Where is the retry policy defined?", receiver_name="explorer")
```

## API

- `await agent_observe.list_agents()` returns `current` and `agents`, the whole
  family, active or not. Each agent carries `sessionId`, optional
  `sessionName`, `relationship` (`parent`/`sibling`/`child`/`relative`),
  `status`, `isSessionActive`, an optional one-line `note` (at most 160 chars:
  its latest final report or `rlm.progress.note`, else its task), and the
  counts and message previews known for it: `latestMessage` for a live
  session, `firstMessage` for an inactive child. A member with no live session
  has no `activeSessionId` and no live detail; message it with
  `agent_message.send` by its `sessionName` (or `parent/child` path, or its
  `sessionId` when it has no name). An idle or inactive agent wakes on a
  message. For direct children, `await rlm.list_subagents()` also exposes
  parent-owned lifecycle handles.
- `await agent_observe.get_agent(target)` returns `agent`, where `agent`
  contains one live agent summary. `target` is resolved like other live-session
  selectors: active id, session id/name, or unambiguous suffix.
- `await agent_observe.recent_messages(target, limit=8, max_chars=800)`
  returns up to `limit` recent bounded message previews for the target session.
  `limit` must be 1-50, and `max_chars` must be 80-2000.

## Safety

- This skill is read-only and exposes no mutation commands.
- Targets outside your family are rejected; transcript reads follow the same
  family rule as messaging.
- Message access is bounded by count and per-message character limit.
- Prefer notes, status, and recent previews for orchestration: route a question
  to the agent that already has the context before redoing its work. Ask the
  user before using observed context to steer another user's session.
