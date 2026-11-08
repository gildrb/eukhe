"""``@remote`` and the wrapped kernel's stdin owner."""

from __future__ import annotations

import subprocess
import sys
import unittest

from test_repl import SRC, ReplProcess

DEFINE = """
import time
from rlm import remote

@remote
def add(a: int, b: int = 2) -> int:
    "Add two numbers."
    return a + b

@remote
def hang():
    time.sleep(3600)
"""


class RemoteSchemaTest(unittest.TestCase):
    def setUp(self) -> None:
        sys.path.insert(0, SRC)
        self.addCleanup(sys.path.remove, SRC)

    def test_outside_a_kernel_the_decorator_only_records_the_function(self):
        from rlm import remote as remote_module_function
        from rlm.remote import _parameters, lookup

        def scale(x: float, factor: int = 2, label: str | None = None, **extra) -> float:
            return x * factor

        self.assertIs(remote_module_function(name="scale_it")(scale), scale)
        self.assertIs(lookup(scale.__module__, scale.__qualname__), scale)
        self.assertEqual(
            _parameters(scale),
            {
                "type": "object",
                "properties": {
                    "x": {"type": "number"},
                    "factor": {"type": "integer"},
                    "label": {"anyOf": [{"type": "string"}, {"type": "null"}]},
                },
                "additionalProperties": True,
                "required": ["x"],
            },
        )

    def test_bad_names_and_positional_parameters_are_refused(self):
        from rlm import remote

        def positional(a, /):
            return a

        def star(*items):
            return items

        with self.assertRaises(ValueError):
            remote(name="has space")(lambda: None)
        with self.assertRaises(TypeError):
            remote(positional)
        with self.assertRaises(TypeError):
            remote(star)


class RemoteCallTest(unittest.TestCase):
    def setUp(self) -> None:
        self.repl = ReplProcess()
        self.addCleanup(self.repl.close)
        self.repl.ready()

    def test_register_call_error_and_timeout_leave_the_kernel_serving(self):
        self.repl.send({"type": "execute", "id": "define", "code": DEFINE})
        registrations = []
        while True:
            event = self.repl.read_event()
            if event.get("event") == "host_request":
                data = dict(event["data"])
                registrations.append({key: data[key] for key in ("type", "name", "module", "function", "description")})
                self.repl.send({"type": "host_reply", "id": event["id"], "data": {"status": "ok", "result": {}}})
            if event.get("event") == "done" and event.get("id") == "define":
                self.assertEqual(event["status"], "ok")
                break
        self.assertEqual(
            registrations,
            [
                {"type": "remote.register", "name": "add", "module": "__main__", "function": "add", "description": "Add two numbers."},
                {"type": "remote.register", "name": "hang", "module": "__main__", "function": "hang", "description": ""},
            ],
        )

        def call(rid: str, function: str, args: dict, timeout_ms: int) -> dict:
            self.repl.send(
                {"type": "call", "id": rid, "module": "__main__", "function": function, "args": args, "timeout_ms": timeout_ms}
            )
            done = self.repl.until_done(rid)[-1]
            done.pop("event")
            return done

        self.assertEqual(call("ok", "add", {"a": 2}, 5000), {"id": "ok", "status": "ok", "result": 4})
        self.assertEqual(
            call("bad", "add", {"a": "x"}, 5000),
            {
                "id": "bad",
                "status": "error",
                "reason": "raised",
                "error": 'TypeError: can only concatenate str (not "int") to str',
            },
        )
        self.assertEqual(
            call("none", "nope", {}, 5000),
            {"id": "none", "status": "error", "reason": "unknown", "error": "__main__.nope is not a @remote function of this kernel"},
        )
        self.assertEqual(
            call("slow", "hang", {}, 200),
            {"id": "slow", "status": "error", "reason": "timeout", "error": "hang did not finish within 200 ms"},
        )
        after = self.repl.execute("after", "1 + 1")
        self.assertEqual([e["text"] for e in after if e.get("event") == "result"], ["2"])
        self.assertEqual(self.repl.shutdown(), 0)

    def test_a_nan_result_and_bad_async_arguments_answer_typed_errors(self):
        code = (
            "from rlm import remote\n"
            "@remote\n"
            "def not_a_number():\n"
            "    return {'x': float('nan')}\n"
            "@remote\n"
            "async def twice(a: int) -> int:\n"
            "    return 2 * a\n"
        )
        self.repl.send({"type": "execute", "id": "define", "code": code})
        while True:
            event = self.repl.read_event()
            if event.get("event") == "host_request":
                self.repl.send({"type": "host_reply", "id": event["id"], "data": {"status": "ok", "result": {}}})
            if event.get("event") == "done" and event.get("id") == "define":
                self.assertEqual(event["status"], "ok")
                break

        def call(rid: str, function: str, args: dict) -> dict:
            self.repl.send({"type": "call", "id": rid, "module": "__main__", "function": function, "args": args})
            events = self.repl.until_done(rid)
            # The typed `done` is the call's one frame: no backstop `error` event.
            self.assertEqual([e["event"] for e in events if e.get("id") == rid], ["done"])
            done = events[-1]
            done.pop("event")
            return done

        nan = call("nan", "not_a_number", {})
        # Newer Pythons append the value (": nan") to the ValueError text.
        error = nan.pop("error", "")
        self.assertEqual(nan, {"id": "nan", "status": "error", "reason": "unencodable"})
        self.assertTrue(
            error.startswith("not_a_number returned a value JSON cannot carry: Out of range float values"), error
        )
        self.assertEqual(
            call("args", "twice", {"b": 1}),
            {
                "id": "args",
                "status": "error",
                "reason": "raised",
                "error": "TypeError: twice() got an unexpected keyword argument 'b'",
            },
        )
        self.assertEqual(call("ok", "twice", {"a": 3}), {"id": "ok", "status": "ok", "result": 6})
        after = self.repl.execute("after", "1 + 1")
        self.assertEqual([e["text"] for e in after if e.get("event") == "result"], ["2"])
        self.assertEqual(self.repl.shutdown(), 0)


class StdinOwnerTest(unittest.TestCase):
    def test_a_stdin_owned_kernel_ignores_the_owner_pid_and_leads_its_group(self):
        gone = subprocess.Popen([sys.executable, "-c", "pass"])
        gone.wait()
        repl = ReplProcess(env={"EUKHE_KERNEL_OWNER": "stdin", "EUKHE_KERNEL_OWNER_PID": str(gone.pid)})
        self.addCleanup(repl.close)
        repl.ready()
        events = repl.execute("probe", "import os\nos.getpgrp() == os.getpid()")
        self.assertEqual([e["text"] for e in events if e.get("event") == "result"], ["True"])
        assert repl.proc.stdin is not None
        repl.proc.stdin.close()
        self.assertEqual(repl.proc.wait(timeout=30), 0)


if __name__ == "__main__":
    unittest.main()
