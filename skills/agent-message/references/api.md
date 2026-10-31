# agent_message API

- `agent_message.send(message: str, broadcast_message: str | None = None, *, receiver_role: Literal["parent", "sibling", "child", "relative"] | None = None, receiver_name: str | None = None) -> dict`: sends one direct text message to one family member.
  - `receiver_name` alone addresses any family agent by session name, id, or `parent/child` path. An ambiguous name fails with the matching ids and paths.
  - `receiver_role` narrows the match to one relationship; `receiver_role="parent"` takes no name.
  - Delivery always steers: a busy target sees the message during its active run.
  - Receipt: `deliveryStatus` (`"delivered"`: reached an idle target's context; `"queued"`: accepted, delivers when the target's current work allows), `deliveredAt` or `queuedAt`, the message id, and `receiverRole` (the target's relationship to you).
  - Broadcast: `send("all", message)` sends to the whole family roster and returns `{receipts: [...]}` in roster order; a failed entry holds the target id and a short `error`. One failure does not undo the others.

## Reach

- The family: every agent under your root session. Root sessions are siblings; another root's subagents are outside it (`No agent in this family matches "..."`).
- A child stays reachable only until its parent session closes.
- The daemon enforces message size, rate and pending-queue limits before it accepts a message.
