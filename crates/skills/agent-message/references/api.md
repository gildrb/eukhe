# agent_message API

- `agent_message.send(message: str, broadcast_message: str | None = None, *, receiver_role: Literal["parent", "child"] | None = None, receiver_name: str | None = None) -> dict`: sends one direct text message to your parent or one of your own children.
  - `receiver_role="parent"` takes no name and reaches your parent (`This agent has no parent to message` at a root).
  - `receiver_name` addresses one of your own children by session name, id, or `parent/child` path; `receiver_role="child"` is optional with it. An ambiguous name fails with the matching ids (`Child selector "..." is ambiguous; address one by id: ...`).
  - Any other `receiver_role` is refused: `receiver_role must be "parent" or "child"; agents message only their parent and their own children`.
  - Delivery always steers: a busy target sees the message during its active run.
  - Receipt: `deliveryStatus` (`"delivered"`: reached an idle target's context; `"queued"`: accepted, delivers when the target's current work allows), `deliveredAt` or `queuedAt`, the message id, and `receiverRole` (`parent` or `child`).
  - Broadcast: `send("all", message)` sends to your own children and returns `{receipts: [...]}` in roster order; a failed entry holds the target id and a short `error`. One failure does not undo the others.
  - Incoming messages are headed `[agent-message from parent:<name>]` or `[agent-message from child:<name>]`.

## Reach

- Your parent and your own children only. Siblings, grandchildren, cousins and other roots are unreachable (`No child of this agent matches "..."; agents message only their parent and their own children`); ask the parent or child that owns them to relay.
- A child stays reachable only until its parent session closes.
- The daemon enforces message size, rate and pending-queue limits before it accepts a message.
