---
name: agent-observe
description: Read-only view of your agent family (every agent under your root session) - list each agent with its status and a one-line note of its latest work, read one agent's detail, or preview its recent messages. Use before you message or spawn, to find the agent that already holds the context, or to check what a child is doing. It never changes another session.
---

# Agent Observe

## Steps

1. Roster: `roster = await agent_observe.list_agents()`. Each row has `relationship`, `sessionName`, `status` and a `note` (its latest report or progress note, else its task).
2. Route: a note that matches your question means that agent has the context. Ask it with `agent_message.send(..., receiver_name=...)` before you redo its work or spawn a new child.
3. Detail, only when the note is not enough: `await agent_observe.get_agent(target)`, then `await agent_observe.recent_messages(target, limit=8)`.

## Rules

- Read-only: it cannot prompt, steer, rename or stop a session. To act, message (agent-message) or use the subagent handles (subagents).
- Prefer notes and status to transcripts: previews cost context.
- Targets outside your family are refused.
- Ask the user before you use what you observe to steer another user's session.

Fields and limits: [references/api.md](references/api.md).
