---
name: agent-message
description: Message any agent of your family (every agent under your root session) through the daemon, by name, id, or parent/child path. Discover reachable agents with agent_observe.list_agents, then send direct text without spoofing sender identity.
---

# Agent Message

Send direct messages to any agent of the current family through the local
daemon. The family is every agent under your root session: your parent, your
siblings, your children, and every other agent in the tree (grandparents,
cousins, grandchildren: `relative`). Root sessions are each other's siblings,
but another root's subagents are outside your family. The daemon derives your
sender identity from the current session; do not try to include a `from`
field.

Call directly from the kernel:

```python
# Ask the agent that already holds the context, wherever it sits in the tree.
receipt = await agent_message.send(
    "Which file defines the retry policy?",
    receiver_name="explorer",
)
# Two branches share a name: use the parent/child path.
await agent_message.send("Re-run the parser tests.", receiver_name="builder/tester")
# The unique parent needs no name.
await agent_message.send("Done; summary in the last cell.", receiver_role="parent")
```

## API

- `await agent_observe.list_agents()` (agent-observe skill) is the roster: every
  agent this skill can reach, active or not, with its `relationship`,
  `sessionName`, and a one-line `note` (its latest report or progress note,
  else its task). Use the note to route a question to the specialist that
  already has the context instead of re-deriving it.
- `await agent_message.send(message, receiver_role=None, receiver_name=None)`
  sends one direct text message to one family member. `receiver_name` alone
  addresses any agent of the family by session name, id, or `parent/child`
  path; an ambiguous name fails with the matching ids and paths, so retry
  with the path. `receiver_role` (`"parent"`, `"sibling"`, `"child"`, or
  `"relative"`) optionally narrows the match to one relationship;
  `receiver_role="parent"` takes no name.
  Sending to an idle, inactive, or completed agent wakes it and starts an
  ordinary follow-up turn in that same session and context. A child remains
  available only until its parent session closes.
  `send("all", message)` broadcasts to the whole family roster and returns
  `{receipts: [...]}` in roster order; successful entries are ordinary receipts
  and failed entries contain the target id and a short `error`. One failed delivery
  does not reject successful deliveries. Messages always use steering delivery so
  a busy target sees them during its active run. Returns a receipt with a
  `deliveryStatus` field: `"delivered"` means the message reached an idle target's
  context; `"queued"` means a steering message was accepted and will deliver when
  the target's current work allows (`send` does not block waiting for that).
  Delivered receipts carry `deliveredAt`, queued receipts carry `queuedAt`;
  `receiverRole` names the target's relationship to you.

## Safety

- Do not delete a child immediately after `send`: delivered follow-ups may still
  be running and queued receipts have not run yet. Wait until observation shows
  the child is idle and its context is no longer needed before calling
  `await rlm.delete_subagent(child)`.
- Reach ends at your family: a name that exists only under another root is
  rejected (`No agent in this family matches "..."`).
- Messages between two subagents are also shown to the root session's user as
  a display-only relay row; they never enter the root's model context.
- Sender identity is daemon-derived and cannot be spoofed from Python.
- The daemon enforces message size, rate, and pending-queue limits before
  accepting delivery.
