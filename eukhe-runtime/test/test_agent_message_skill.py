from __future__ import annotations

import asyncio
import importlib.util
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch


SKILL = Path(__file__).parents[2] / "skills/agent-message/src/agent_message/__init__.py"


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, SKILL)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class AgentMessageSkillTest(unittest.TestCase):
    def test_roled_mesh_and_broadcast_forms(self) -> None:
        module = _load("agent_message_test")
        host = AsyncMock(return_value={"deliveryStatus": "queued"})
        with patch.object(module, "host_request", host), patch.object(module, "_emit_sent_message"):
            asyncio.run(module.send("done", receiver_role="parent"))
            asyncio.run(module.send("all", "follow up"))
            asyncio.run(module.send("who owns the parser?", receiver_name="scout/parser"))
            asyncio.run(module.send("ping", receiver_role="relative", receiver_name="helper"))
        self.assertEqual(
            [call.args for call in host.await_args_list],
            [
                ("agent_message.send", {"message": "done", "receiver_role": "parent"}),
                ("agent_message.send", {"target": "all", "message": "follow up"}),
                (
                    "agent_message.send",
                    {"message": "who owns the parser?", "receiver_name": "scout/parser"},
                ),
                (
                    "agent_message.send",
                    {"message": "ping", "receiver_role": "relative", "receiver_name": "helper"},
                ),
            ],
        )

    def test_roled_selector_validation(self) -> None:
        module = _load("agent_message_validation")
        with self.assertRaisesRegex(ValueError, "required"):
            asyncio.run(module.send("hello", receiver_role="child"))
        with self.assertRaisesRegex(ValueError, "required"):
            asyncio.run(module.send("hello"))
        with self.assertRaisesRegex(ValueError, "omitted"):
            asyncio.run(module.send("hello", receiver_role="parent", receiver_name="x"))
        with self.assertRaisesRegex(ValueError, "receiver_role must be"):
            asyncio.run(module.send("hello", receiver_role="uncle", receiver_name="x"))
        with self.assertRaisesRegex(TypeError, "unexpected keyword argument 'mode'"):
            asyncio.run(module.send("hello", receiver_role="parent", mode="follow_up"))


if __name__ == "__main__":
    unittest.main()
