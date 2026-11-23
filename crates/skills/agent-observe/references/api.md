# agent_observe API

- `agent_observe.list_agents() -> dict`: `current` and `agents`: your own row, your parent and your own children, active or not. Siblings, grandchildren and other roots are never listed. Each agent: `sessionId`, optional `sessionName`, `relationship` (`parent`/`child`), `status`, `isSessionActive`, an optional `note` (at most 160 characters: its latest final report or progress note, else its task), and known counts and previews (`latestMessage` for a live session, `firstMessage` for an inactive child). A member with no live session has no `activeSessionId`; message a child by `sessionName`, `parent/child` path, or `sessionId`, and the parent with `receiver_role="parent"`.
- `agent_observe.get_agent(target: str) -> dict`: `agent`, one live agent summary. `target`: active id, session id or name, or an unambiguous suffix. An inactive child is loaded before the read.
- `agent_observe.recent_messages(target: str, limit: int = 8, max_chars: int = 800) -> dict`: up to `limit` recent message previews. `limit` must be 1-50 and `max_chars` 80-2000, else an error.

For direct children, `rlm.list_subagents()` (subagents skill) also gives the lifecycle handles.
