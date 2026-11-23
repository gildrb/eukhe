# rlm_heartbeat API

- `rlm_heartbeat.create(instruction: str, interval: str | None = None, label: str | None = None, delivery_mode: Literal["steer", "follow_up"] | None = None) -> dict`: a new recurring heartbeat for this session. `interval` is a schedule string (default: every 5 minutes). Several may run at once.
- `rlm_heartbeat.list(include_inactive: bool = False) -> dict`: this session's heartbeats; by default active and paused ones.
- `rlm_heartbeat.update(id: str, instruction: str | None = None, interval: str | None = None, label: str | None = None, status: Literal["pause", "resume"] | None = None, delivery_mode: Literal["steer", "follow_up"] | None = None) -> dict`: changes one heartbeat.
- `rlm_heartbeat.delete(id: str) -> dict`: cancels one heartbeat.

An unparsable schedule or a wrong `delivery_mode` is refused with the reason. These heartbeats never read or change the user's `/heartbeat`, and they end with the session.
