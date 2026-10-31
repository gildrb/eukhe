from __future__ import annotations

import importlib
import unittest
from unittest.mock import Mock, patch

rlm_module = importlib.import_module("rlm")


def _entry(entry_id: int, kind: str, text: str, **extra: object) -> dict[str, object]:
    return {"id": entry_id, "kind": kind, "text": text, "tool_calls": [], "timestamp": None, **extra}


class HistoryTest(unittest.TestCase):
    def test_entries_page_through_the_history_as_values(self) -> None:
        pages = [
            {"entries": [_entry(1, "user", "hi")], "next": 1},
            {
                "entries": [
                    _entry(
                        2,
                        "assistant",
                        "",
                        tool_calls=[{"id": "c1", "name": "ipython", "arguments": {"code": "x = 1"}}],
                    ),
                    _entry(3, "tool_result", "ok", tool_call_id="c1", tool_name="ipython", is_error=False),
                ],
                "next": None,
            },
        ]
        request = Mock(side_effect=pages)
        with patch.object(rlm_module, "host_request_sync", request):
            entries = rlm_module.history.entries()

        self.assertEqual(
            entries,
            [
                rlm_module.HistoryEntry(id=1, kind="user", text="hi"),
                rlm_module.HistoryEntry(
                    id=2,
                    kind="assistant",
                    text="",
                    tool_calls=(rlm_module.ToolCall("c1", "ipython", {"code": "x = 1"}),),
                ),
                rlm_module.HistoryEntry(
                    id=3, kind="tool_result", text="ok", tool_call_id="c1", tool_name="ipython", is_error=False
                ),
            ],
        )
        self.assertEqual(
            [call.args for call in request.call_args_list],
            [("history.entries", {"limit": 256}), ("history.entries", {"limit": 256, "after": 1})],
        )

    def test_compactions_keep_their_summary_and_first_kept_entry(self) -> None:
        request = Mock(
            return_value={"entries": [_entry(9, "compaction", "the summary", first_kept_id=7)], "next": None}
        )
        with patch.object(rlm_module, "host_request_sync", request):
            compactions = rlm_module.history.compactions()

        self.assertEqual(compactions, [rlm_module.HistoryEntry(id=9, kind="compaction", text="the summary", first_kept_id=7)])
        request.assert_called_once_with("history.entries", {"limit": 256, "kind": "compaction"})

    def test_entry_reads_one_entry(self) -> None:
        request = Mock(return_value={"entry": _entry(4, "user", "again")})
        with patch.object(rlm_module, "host_request_sync", request):
            entry = rlm_module.history.entry(4)

        self.assertEqual(entry, rlm_module.HistoryEntry(id=4, kind="user", text="again"))
        request.assert_called_once_with("history.entry", {"id": 4})


class ChatTest(unittest.TestCase):
    def test_view_and_zoom_return_lines_as_tuples(self) -> None:
        request = Mock(
            side_effect=[
                {"lines": [{"id": 0, "n": 2, "text": "user: a eukhe: b"}], "messages": 2},
                {"lines": [{"id": 0, "n": 1, "text": "user: a"}, {"id": 1, "n": 1, "text": "eukhe: b"}]},
                {"text": "user: a"},
            ]
        )
        with patch.object(rlm_module, "host_request_sync", request):
            view = rlm_module.chat.view()
            halves = rlm_module.chat.zoom(0, 2)
            message = rlm_module.chat.message(0)

        self.assertEqual(view, [(0, 2, "user: a eukhe: b")])
        self.assertEqual(halves, [rlm_module.ChatLine(0, 1, "user: a"), rlm_module.ChatLine(1, 1, "eukhe: b")])
        self.assertEqual(message, "user: a")
        self.assertEqual(
            [call.args for call in request.call_args_list],
            [("chat.view", None), ("chat.zoom", {"id": 0, "n": 2}), ("chat.zoom", {"id": 0, "n": 1})],
        )

    def test_chat_has_no_search(self) -> None:
        with self.assertRaisesRegex(AttributeError, "chat has no search: the chat memory is read by zoom only"):
            rlm_module.chat.search("anything")

    def test_zoom_of_one_message_points_to_message(self) -> None:
        with self.assertRaisesRegex(ValueError, "chat.message"):
            rlm_module.chat.zoom(3, 1)


if __name__ == "__main__":
    unittest.main()
