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


class EditTest(unittest.TestCase):
    def test_rejection_is_edit_rejected(self) -> None:
        reply = {"outcome": "rejected", "version": "edit@hl.1", "reason": "parse", "message": "bad op"}
        with patch.object(rlm, "host_request_sync", return_value=reply):
            with self.assertRaises(fs.EditRejected) as caught:
                fs.edit("[a.py#1A2B]\nNOPE")
        self.assertEqual((caught.exception.version, caught.exception.reason), ("edit@hl.1", "parse"))

    def test_exact_string_dialect_is_refused_with_the_hashline_form(self) -> None:
        with self.assertRaisesRegex(TypeError, "edit\\(\\) does not take 'old_str': edit\\(\\) takes a hashline patch"):
            fs.edit(old_str="a", new_str="b")

    def test_done_edit_exposes_new_headers(self) -> None:
        reply = {
            "outcome": "done",
            "version": "edit@hl.1",
            "rendered": "[a.py#3C4D]\n...",
            "files": [{"path": "a.py", "tag": "3C4D", "change": "updated"}],
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            result = fs.edit(input="[a.py#1A2B]\nPUT 1.=1:\n+y = 2")
        host.assert_called_once_with("fs.edit", {"input": "[a.py#1A2B]\nPUT 1.=1:\n+y = 2", "cwd": os.getcwd()})
        self.assertEqual((result.headers, result.warnings), (["[a.py#3C4D]"], ["Repaired argument: input= read as patch="]))


class SearchTest(unittest.TestCase):
    def test_grep_returns_hits_that_print_as_rows(self) -> None:
        reply = {
            "outcome": "done",
            "version": "grep@1",
            "rendered": "[a.py#1A2B]\n*1:x = 1",
            "files": [{"path": "a.py", "absolute": "/w/a.py", "tag": "1A2B", "matches": [[1, "x = 1"]]}],
            "total_files": 1,
            "more_files": False,
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            hits = fs.grep(regex="x", ignore_case="true")
        self.assertEqual(host.call_args.args[1]["ignore_case"], True)
        self.assertEqual(list(hits), [fs.Hit(path="a.py", tag="1A2B", line=1, text="x = 1")])
        self.assertEqual(str(hits).splitlines()[0], "[a.py#1A2B]")

    def test_glob_joins_the_base_path(self) -> None:
        reply = {"outcome": "done", "version": "glob@1", "rendered": "a.py", "paths": ["src/a.py"], "truncated": False}
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            paths = fs.glob("*.py;*.pyi", "src")
        self.assertEqual(host.call_args.args[1]["path"], "src/*.py;src/*.pyi")
        self.assertEqual(paths, ["src/a.py"])


if __name__ == "__main__":
    unittest.main()
