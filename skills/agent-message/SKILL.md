---
name: agent-message
description: Send a direct text message to one agent of your family (parent, sibling, child, or any agent under your root session) by name, id or parent/child path, or broadcast to the whole family. Use to ask the agent that already holds the context instead of re-deriving it, to reply to your parent, or to steer a running child. Find the right recipient first with agent-observe.
---

# Agent Message

## Steps

1. Pick the recipient: `await agent_observe.list_agents()` and read each `note`. Ask the agent whose note shows it already has the context.
2. Send: `await agent_message.send("Which file defines the retry policy?", receiver_name="explorer")`. Your parent needs no name: `receiver_role="parent"`.
3. Ambiguous name: the error lists the matching ids and paths; resend with the path (`"builder/tester"`).
4. Need an answer: say so in the message. Not every message needs a reply.
5. Read the receipt: `delivered` reached an idle agent; `queued` waits for the busy agent's current work. Do not wait on it; the reply arrives as a message.

## Rules

- A message to an idle, inactive or completed agent wakes it for a follow-up turn in its own context.
- Do not delete a child right after `send`: the follow-up may still run.
- Only message siblings when it is clearly needed.
- Your identity is set by the daemon; never add a sender field.
- Size, rate and queue limits refuse a message with the reason; shorten it or wait.
- Messages between two subagents show to the root user as display-only rows; they never enter the root's context.

Signature, receipts and broadcast: [references/api.md](references/api.md).
