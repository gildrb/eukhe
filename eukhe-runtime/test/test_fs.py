from __future__ import annotations

import os
import unittest
from unittest.mock import patch

import rlm
from rlm import fs

READ_REPLY = {
    "outcome": "done",
    "version": "read@1",
    "path": "a.py",
    "absolute": "/w/a.py",
    "kind": "file",
    "rendered": "[a.py#1A2B]\n1:x = 1",
    "diags": [],
    "tag": "1A2B",
    "text": "x = 1\n",
    "total_lines": 1,
    "shown": [[1, 1]],
}


class ReadTest(unittest.TestCase):
    def test_read_sends_cwd_and_selector_and_prints_projection(self) -> None:
        with patch.object(rlm, "host_request_sync", return_value=READ_REPLY) as host:
            doc = fs.read("a.py", "1-5")
        host.assert_called_once_with("fs.read", {"path": "a.py:1-5", "cwd": os.getcwd()})
        self.assertEqual(
            (str(doc), doc.header, doc.lines, doc.shown),
            ("[a.py#1A2B]\n1:x = 1", "[a.py#1A2B]", ["x = 1"], [(1, 1)]),
        )

    def test_aliases_and_string_numbers_are_repaired_with_warnings(self) -> None:
        with patch.object(rlm, "host_request_sync", return_value=READ_REPLY):
            doc = fs.read(file_path="a.py")
        self.assertEqual(doc.warnings, ["Repaired argument: file_path= read as path="])
        self.assertEqual(
            str(doc),
            "[a.py#1A2B]\n1:x = 1\nWarnings:\n- Repaired argument: file_path= read as path=",
        )

    def test_unknown_keyword_lists_the_valid_ones(self) -> None:
        with self.assertRaisesRegex(TypeError, "unexpected keyword argument 'paths'; valid: path, sel"):
            fs.read(paths="a.py")

    def test_rejection_raises_fs_error_with_reason(self) -> None:
        reply = {"outcome": "rejected", "version": "read@1", "reason": "not_found", "message": "Path 'b' not found"}
        with patch.object(rlm, "host_request_sync", return_value=reply):
            with self.assertRaises(fs.FsError) as caught:
                fs.read("b")
        self.assertEqual((caught.exception.reason, str(caught.exception)), ("not_found", "Path 'b' not found"))


class CoerceTest(unittest.TestCase):
    def test_bool_and_int_spellings(self) -> None:
        repairs: list[str] = []
        self.assertEqual(
            (fs._coerce("flag", "true", bool, repairs), fs._coerce("n", "3", int | None, repairs)),
            (True, 3),
        )
        self.assertEqual(repairs, ["flag='true' read as True", "n='3' read as 3"])


class WriteTest(unittest.TestCase):
    def test_write_aliases_content(self) -> None:
        reply = {
            "outcome": "done",
            "version": "write@1",
            "path": "b.txt",
            "absolute": "/w/b.txt",
            "created": True,
            "bytes": 3,
            "tag": "9F3E",
            "made_executable": False,
            "rendered": "[b.txt#9F3E]\nSuccessfully wrote 3 bytes to b.txt",
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            result = fs.write("b.txt", text="hi\n")
        host.assert_called_once_with("fs.write", {"path": "b.txt", "content": "hi\n", "cwd": os.getcwd()})
        self.assertEqual((result.header, result.warnings), ("[b.txt#9F3E]", ["Repaired argument: text= read as content="]))


if __name__ == "__main__":
    unittest.main()
