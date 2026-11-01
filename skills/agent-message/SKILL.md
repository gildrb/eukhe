---
name: agent-message
description: Send a direct text message to your parent or one of your own children (by name, id or parent/child path), or broadcast to all your children. Agents message only their parent and their own children; siblings and other relatives are unreachable. Use to reply to your parent, to ask a child that already holds the context, or to steer a running child. Find the right child first with agent-observe.
---

# Agent Message

## Steps

1. Pick the recipient: `await agent_observe.list_agents()` lists you, your parent and your children; read each child's `note`. Ask the child whose note shows it already has the context.
2. Send to a child: `await agent_message.send("Which file defines the retry policy?", receiver_name="explorer")` (optionally `receiver_role="child"`). Your parent needs no name: `receiver_role="parent"`.
3. Ambiguous child name: the error lists the matching ids; resend with one id or the `parent/child` path.
4. Need an answer: say so in the message. Not every message needs a reply.
5. Read the receipt: `delivered` reached an idle agent; `queued` waits for the busy agent's current work. Do not wait on it; the reply arrives as a message.

## Rules

- A message to an idle, inactive or completed agent wakes it for a follow-up turn in its own context.
- Do not delete a child right after `send`: the follow-up may still run.
- Reach is your parent and your own children only. Siblings, grandchildren and other roots are refused (`No child of this agent matches "..."`); route through the parent or child that owns them.
- Your identity is set by the daemon; never add a sender field.
- Size, rate and queue limits refuse a message with the reason; shorten it or wait.

Signature, receipts and broadcast: [references/api.md](references/api.md).
