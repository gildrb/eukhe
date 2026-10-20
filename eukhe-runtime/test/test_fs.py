from __future__ import annotations

import os
import unittest
from typing import Any
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
    "warnings": [],
}


def _sent(host: Any) -> dict[str, Any]:
    request_type, payload = host.call_args.args
    return {"type": request_type, **payload}


class ReadTest(unittest.TestCase):
    def test_read_sends_cwd_and_arguments_and_prints_projection(self) -> None:
        with patch.object(rlm, "host_request_sync", return_value=READ_REPLY) as host:
            doc = fs.read("a.py:1-5")
        host.assert_called_once_with("fs.read", {"cwd": os.getcwd(), "args": {"path": "a.py:1-5"}})
        self.assertEqual(
            (str(doc), doc.header, doc.lines, doc.shown),
            ("[a.py#1A2B]\n1:x = 1", "[a.py#1A2B]", ["x = 1"], [(1, 1)]),
        )

    def test_keywords_go_to_the_host_as_given_and_its_repairs_print(self) -> None:
        reply = {**READ_REPLY, "warnings": ["Repaired argument: file_path read as path"]}
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            doc = fs.read(file_path="a.py")
        self.assertEqual(_sent(host)["args"], {"file_path": "a.py"})
        self.assertEqual(
            str(doc),
            "[a.py#1A2B]\n1:x = 1\nWarnings:\n- Repaired argument: file_path read as path",
        )

    def test_positional_and_keyword_for_one_argument_is_a_type_error(self) -> None:
        with self.assertRaisesRegex(TypeError, "multiple values for argument 'path'"):
            fs.read("a.py", path="b.py")
        with self.assertRaisesRegex(TypeError, "at most 1 positional"):
            fs.read("a.py", "1-5")

    def test_rejection_raises_fs_error_with_reason(self) -> None:
        reply = {"outcome": "rejected", "version": "read@1", "reason": "arguments", "message": "read has no argument `paths`"}
        with patch.object(rlm, "host_request_sync", return_value=reply):
            with self.assertRaises(fs.FsError) as caught:
                fs.read(paths="b")
        self.assertEqual((caught.exception.reason, str(caught.exception)), ("arguments", "read has no argument `paths`"))


class WriteTest(unittest.TestCase):
    def test_write_sends_path_and_content(self) -> None:
        reply = {
            "outcome": "done",
            "version": "write@1",
            "path": "b.txt",
            "absolute": "/w/b.txt",
            "created": True,
            "bytes": 3,
            "tag": "9F3E",
            "rendered": "[b.txt#9F3E]\nSuccessfully wrote 3 bytes to b.txt",
            "warnings": [],
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            result = fs.write("b.txt", "hi\n")
        self.assertEqual(_sent(host)["args"], {"path": "b.txt", "content": "hi\n"})
        self.assertEqual((result.header, str(result)), ("[b.txt#9F3E]", reply["rendered"]))


class EditTest(unittest.TestCase):
    def test_rejection_is_edit_rejected(self) -> None:
        reply = {"outcome": "rejected", "version": "edit@hl.1", "reason": "parse", "message": "bad op"}
        with patch.object(rlm, "host_request_sync", return_value=reply):
            with self.assertRaises(fs.EditRejected) as caught:
                fs.edit("[a.py#1A2B]\nNOPE")
        self.assertEqual((caught.exception.version, caught.exception.reason), ("edit@hl.1", "parse"))

    def test_done_edit_exposes_new_headers(self) -> None:
        reply = {
            "outcome": "done",
            "version": "edit@hl.1",
            "rendered": "[a.py#3C4D]\n...",
            "files": [{"path": "a.py", "tag": "3C4D", "change": "updated"}],
            "warnings": [],
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            result = fs.edit("[a.py#1A2B]\nPUT 1.=1:\n+y = 2")
        self.assertEqual(_sent(host)["args"], {"input": "[a.py#1A2B]\nPUT 1.=1:\n+y = 2"})
        self.assertEqual(result.headers, ["[a.py#3C4D]"])


class SearchTest(unittest.TestCase):
    def test_grep_returns_hits_that_print_as_rows(self) -> None:
        reply = {
            "outcome": "done",
            "version": "grep@1",
            "rendered": "[a.py#1A2B]\n*1:x = 1",
            "files": [{"path": "a.py", "absolute": "/w/a.py", "tag": "1A2B", "matches": [[1, "x = 1"]]}],
            "total_files": 1,
            "more_files": False,
            "warnings": [],
        }
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            hits = fs.grep("x", "src", case=False)
        self.assertEqual(_sent(host)["args"], {"pattern": "x", "path": "src", "case": False})
        self.assertEqual(list(hits), [fs.Hit(path="a.py", tag="1A2B", line=1, text="x = 1")])
        self.assertEqual(str(hits).splitlines()[0], "[a.py#1A2B]")

    def test_glob_sends_the_path_list(self) -> None:
        reply = {"outcome": "done", "version": "glob@1", "rendered": "a.py", "paths": ["src/a.py"], "truncated": False, "warnings": []}
        with patch.object(rlm, "host_request_sync", return_value=reply) as host:
            paths = fs.glob("src/*.py;src/*.pyi")
        self.assertEqual(_sent(host)["args"], {"path": "src/*.py;src/*.pyi"})
        self.assertEqual(paths, ["src/a.py"])


if __name__ == "__main__":
    unittest.main()
