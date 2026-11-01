"""Eukhe session-to-session messaging skill.

All routing and sender identity live in the Eukhe daemon. These functions
only call the host bridge exposed inside the Eukhe kernel.
"""

from __future__ import annotations

from typing import Any, Literal

from rlm import host_request

ReceiverRole = Literal["parent", "child"]
_ROLES = ("parent", "child")
_MESSAGE_DISPLAY_MIME = "application/vnd.eukhe.agent-message+json"


async def send(
    message: str,
    broadcast_message: str | None = None,
    *,
    receiver_role: ReceiverRole | str | None = None,
    receiver_name: str | None = None,
) -> dict[str, Any]:
    """Send one message to the parent or one own child, or broadcast to ``"all"`` children.

    Agents message only their parent and their own children. ``receiver_role="parent"``
    takes no name; ``receiver_name`` addresses one own child by name, id, or
    ``parent/child`` path (``receiver_role="child"`` is optional with it).
    """
    if broadcast_message is not None:
        if message != "all":
            raise TypeError(
                "positional agent_message.send targets are not supported; "
                "use receiver_role and receiver_name"
            )
        if receiver_role is not None or receiver_name is not None:
            raise TypeError("broadcast cannot be combined with receiver_role/receiver_name")
        payload: dict[str, Any] = {
            "target": "all",
            "message": broadcast_message,
        }
    else:
        if receiver_role is not None and receiver_role not in _ROLES:
            raise ValueError(
                'agent_message.send receiver_role must be "parent" or "child"; '
                "agents message only their parent and their own children"
            )
        if not isinstance(message, str):
            raise TypeError(f"message must be str, got {type(message).__name__}")
        if receiver_role == "parent":
            if receiver_name is not None:
                raise ValueError("receiver_name must be omitted for parent messages")
        elif not isinstance(receiver_name, str) or not receiver_name.strip():
            raise ValueError(
                "receiver_name is required: an agent name, id, or parent/child path "
                '(only receiver_role="parent" needs no name)'
            )
        payload = {"message": message}
        if receiver_role is not None:
            payload["receiver_role"] = receiver_role
        if receiver_name is not None:
            payload["receiver_name"] = receiver_name
    receipt = await host_request("agent_message.send", payload)
    receipts = receipt.get("receipts") if isinstance(receipt, dict) else None
    if isinstance(receipts, list):
        for item in receipts:
            if isinstance(item, dict) and "deliveryStatus" in item:
                _emit_sent_message(item)
    else:
        _emit_sent_message(receipt)
    return receipt


def _emit_sent_message(receipt: dict[str, Any]) -> None:
    try:
        from rlm import emit

        label = (
            "Agent message queued"
            if receipt.get("deliveryStatus") == "queued"
            else "Agent message sent"
        )
        emit(
            {
                _MESSAGE_DISPLAY_MIME: dict(receipt),
                "text/plain": label,
            }
        )
    except Exception:
        pass
