from __future__ import annotations

import asyncio
import json
import os
import resource
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from unittest import mock

from rlm import bash

# The package re-exports the bash() function under the same name, so reach the
# module through sys.modules for internals.
bash_module = sys.modules["rlm.bash"]


class BashTest(unittest.IsolatedAsyncioTestCase):
    async def test_activity_handles_are_scoped_and_tail_is_bounded(self):
        handle = bash("printf 'first\nsecond\n'; sleep 20")
        from rlm.bash import activity_request

        activity_id = handle._activity_id
        rows = activity_request("list")["activities"]
        listed = next(row for row in rows if row["id"] == activity_id)
        self.assertEqual(listed["pid"], handle.pid)
        self.assertIsNone(listed["exitCode"])
        self.assertIn("T", listed["startedAt"])
        for _ in range(100):
            if "second" in activity_request("tail", activity_id, 1)["tail"]:
                break
            await asyncio.sleep(0.01)
        self.assertEqual(activity_request("tail", activity_id, 1)["tail"], "second")
        self.assertEqual(activity_request("kill", activity_id)["killed"], True)
        await handle
        finished = next(
            row for row in activity_request("list")["activities"] if row["id"] == activity_id
        )
        self.assertEqual(finished["status"], "finished")
        self.assertIsInstance(finished["exitCode"], int)
        with self.assertRaises(KeyError):
            activity_request("kill", "not-a-handle")
        with self.assertRaises(ValueError):
            activity_request("tail", activity_id, 201)
        self.assertFalse(activity_request("kill", activity_id)["killed"])

    async def test_activity_tail_frame_stays_under_the_wire_cap(self):
        # json escaping can expand one byte to six (\uXXXX), so the cap
        # must hold on the serialized frame, not the decoded slice.
        handle = bash('python3 -c "print(chr(0) * 20000)"')
        await handle
        from rlm.bash import activity_request

        activity_id = handle._activity_id
        tail = activity_request("tail", activity_id, 200)["tail"]
        self.assertGreater(len(tail), 0)
        self.assertLessEqual(len(json.dumps({"tail": tail})), 16_384)

    async def test_activity_list_frame_stays_under_the_wire_cap(self):
        handles = [bash("sleep 3 # " + str(index) * 80) for index in range(30)]
        try:
            from rlm.bash import activity_request

            rows = activity_request("list")["activities"]
            self.assertGreater(len(rows), 1)
            self.assertLessEqual(len(json.dumps({"activities": rows})), 16_384)
            self.assertTrue(all(len(row["command"]) <= 512 for row in rows))
        finally:
            for handle in handles:
                handle.kill()

    async def test_activity_tail_keeps_the_newest_output_under_the_cap(self):
        # Escaped output shrinks from the oldest end: the newest line is
        # always the surviving one.
        handle = bash('python3 -c "print(chr(0) * 20000); print(chr(65) * 8)"')
        await handle
        from rlm.bash import activity_request

        activity_id = handle._activity_id
        tail = activity_request("tail", activity_id, 200)["tail"]
        self.assertTrue(tail.endswith("AAAAAAAA"), tail[-60:])
        self.assertLessEqual(len(json.dumps({"tail": tail})), 16_384)

    async def test_await_returns_result(self):
        result = await bash("echo hi")
        self.assertEqual(result.exit_code, 0)
        self.assertIn("hi", result.output)
        self.assertGreaterEqual(result.duration, 0)

        handle = bash("echo again")
        awaited = await handle
        self.assertEqual(handle.poll(), awaited)

    async def test_status_pipe_survives_high_fds_and_strict_posix_shell(self):
        # Regression: dash rejects multi-digit fds in redirections at parse
        # time, so the script must never reference the raw status-pipe fd.
        dummies = [os.open(os.devnull, os.O_RDONLY) for _ in range(30)]
        self.addCleanup(lambda: [os.close(fd) for fd in dummies])
        if os.path.exists("/bin/dash"):
            with mock.patch.dict(os.environ, {"EUKHE_BASH_SHELL": "/bin/dash"}):
                result = await bash("echo ok")
            self.assertEqual(result.exit_code, 0)
            self.assertIn("ok", result.output)
        result = await bash("echo ok-default")
        self.assertEqual(result.exit_code, 0)
        self.assertIn("ok-default", result.output)

    async def test_backgrounded_tail_and_kill(self):
        handle = bash("echo start; sleep 30")
        self.assertIsNone(handle.poll())
        for _ in range(100):
            if "start" in handle.tail():
                break
            await asyncio.sleep(0.05)
        self.assertIn("start", handle.tail())
        self.assertTrue(handle.running)
        handle.kill(grace=0.2)
        result = await asyncio.wait_for(handle, timeout=5)
        self.assertNotEqual(result.exit_code, 0)

    async def test_kill_escalates_to_sigkill(self):
        handle = bash("trap '' TERM; echo up; sleep 30")
        for _ in range(100):
            if "up" in handle.output():
                break
            await asyncio.sleep(0.05)
        handle.kill(grace=0.2)
        result = await asyncio.wait_for(handle, timeout=10)
        self.assertEqual(result.exit_code, -9)

    async def test_buffer_cap_keeps_head_and_tail(self):
        result = await bash("seq 1 400000")
        self.assertLessEqual(len(result.output), 2 * 1024 * 1024 + 256)
        self.assertTrue(result.output.startswith("1\n"))
        self.assertIn("400000", result.output)
        self.assertIn("bytes dropped", result.output)

    def test_child_env_is_non_interactive(self):
        """Agent shells have no usable stdin: interactive prompts (git commit
        opening $EDITOR, credential asks, pagers) can only hang. _child_env()
        must neutralize them, overriding inherited terminal settings."""
        with mock.patch.dict(
            os.environ,
            {
                "EDITOR": "vim",
                "PAGER": "less",
                "GIT_SEQUENCE_EDITOR": "vim",
                "GIT_ASKPASS": "/usr/bin/git-credential-manager",
                "SSH_ASKPASS_REQUIRE": "force",
            },
        ):
            env = bash_module._child_env()
        self.assertEqual(env["GIT_EDITOR"], "true")
        self.assertEqual(env["GIT_SEQUENCE_EDITOR"], "true")
        self.assertEqual(env["EDITOR"], "true")
        self.assertEqual(env["VISUAL"], "true")
        self.assertEqual(env["GIT_TERMINAL_PROMPTS"], "0")
        self.assertEqual(env["GIT_ASKPASS"], "true")
        self.assertEqual(env["SSH_ASKPASS_REQUIRE"], "never")
        self.assertEqual(env["PAGER"], "cat")
        self.assertEqual(env["GIT_PAGER"], "cat")
        self.assertEqual(env["DEBIAN_FRONTEND"], "noninteractive")

    async def test_spawned_shell_receives_non_interactive_env(self):
        handle = bash(
            'echo "$GIT_EDITOR|$GIT_SEQUENCE_EDITOR|$GIT_TERMINAL_PROMPTS|$GIT_ASKPASS|$SSH_ASKPASS_REQUIRE"'
        )
        result = await handle
        self.assertEqual(result.exit_code, 0)
        self.assertIn("true|true|0|true|never", result.output)

    async def test_env_prefix_and_journal(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_BASH_COMMAND_PREFIX": "echo prefixed",
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                handle = bash('echo "$NO_COLOR $TERM"')
                result = await handle
                # The inactive record lands slightly after finalize, once the group exits.
                records = await _poll_journal(journal, count=2)
            self.assertEqual(result.exit_code, 0)
            lines = result.output.splitlines()
            self.assertEqual(lines[0], "prefixed")
            self.assertIn("1 dumb", lines[1])

            self.assertEqual([r["active"] for r in records], [True, False])
            for record in records:
                self.assertEqual(record["pid"], handle.pid)
                self.assertEqual(record["ownerPid"], os.getpid())
                self.assertEqual(record["kernelPid"], os.getpid())
            self.assertTrue(records[0]["processStartId"].startswith(("proc:", "ps:")))

    async def test_await_returns_when_shell_backgrounds_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                handle = bash("echo fg; sleep 30 &")
                result = await asyncio.wait_for(handle, timeout=5)
                self.assertEqual(result.exit_code, 0)
                self.assertIn("fg", result.output)
                # The shell stays alive as group leader, anchoring its background job.
                os.killpg(handle.pid, 0)
                records = await _poll_journal(journal, count=1)
                self.assertTrue(records[-1]["active"])
                handle.kill(signal.SIGKILL)
                records = await _poll_journal(journal, count=2)
            self.assertFalse(records[-1]["active"])

    async def test_early_shell_exit_returns_and_kills_group(self):
        handle = bash("sleep 30 & exit 7")
        result = await asyncio.wait_for(handle, timeout=5)
        self.assertEqual(result.exit_code, 7)
        # The leader died without draining, so the stale group must be killed.
        await _poll_group_dead(handle.pid)

    async def test_term_ignoring_child_is_escalated(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                handle = bash("sh -c 'trap \"\" TERM; echo ready; sleep 30' &")
                await asyncio.wait_for(handle, timeout=5)
                for _ in range(100):
                    if "ready" in handle.output():
                        break
                    await asyncio.sleep(0.05)
                handle.kill(signal.SIGTERM)
                records = await _poll_journal(journal, count=2, timeout=10)
            self.assertFalse(records[-1]["active"])
            await _poll_group_dead(handle.pid)

    async def test_delivered_status_wins_when_shell_dies_during_completion(self):
        entered = threading.Event()
        release = threading.Event()
        original = bash_module.BashHandle._wait_for_completion

        def held_completion(handle_self):
            output = original(handle_self)
            entered.set()
            release.wait(10)
            return output

        with mock.patch.object(
            bash_module.BashHandle, "_wait_for_completion", held_completion
        ):
            # Background job keeps the shell alive in `wait` after status 0 is delivered.
            handle = bash("sleep 30 & true")
            try:
                self.assertTrue(await asyncio.to_thread(entered.wait, 5))
                os.kill(handle.pid, signal.SIGTERM)
                # _watch must fully finish its finalize decision while _report is held.
                for _ in range(200):
                    with bash_module._live_lock:
                        if handle not in bash_module._live_handles:
                            break
                    await asyncio.sleep(0.05)
                else:
                    self.fail("watcher did not complete while reporter was held")
            finally:
                release.set()
            result = await asyncio.wait_for(handle, timeout=5)
        self.assertEqual(result.exit_code, 0)

    async def test_delivered_status_wins_when_reporter_is_slow(self):
        parsed = threading.Event()
        release = threading.Event()
        original = bash_module.BashHandle._read_status

        def slow_read(handle_self):
            # Pause after read+parse but before the status is reserved, longer
            # than the old 1.0s _watch timeout, while the shell dies.
            status = original(handle_self)
            parsed.set()
            release.wait(10)
            return status

        with mock.patch.object(bash_module.BashHandle, "_read_status", slow_read):
            # Background job keeps the shell alive in `wait` after status 0 is written.
            handle = bash("sleep 30 & true")
            try:
                self.assertTrue(await asyncio.to_thread(parsed.wait, 5))
                os.kill(handle.pid, signal.SIGTERM)
                # Outlast the old timeout so a timed wait would have finalized -15.
                await asyncio.sleep(1.5)
                self.assertIsNone(handle.poll())
            finally:
                release.set()
            result = await asyncio.wait_for(handle, timeout=5)
        self.assertEqual(result.exit_code, 0)

    async def test_status_survives_pipe_fds_above_fd_setsize(self):
        # select.select() rejects fds >= FD_SETSIZE (1024); the delivered status
        # must still win when the status/wake pipes land above that boundary.
        limits = resource.getrlimit(resource.RLIMIT_NOFILE)
        if limits[0] < 1100:
            try:
                resource.setrlimit(resource.RLIMIT_NOFILE, (1100, limits[1]))
            except (ValueError, OSError):
                self.skipTest("cannot raise RLIMIT_NOFILE above FD_SETSIZE")
            self.addCleanup(resource.setrlimit, resource.RLIMIT_NOFILE, limits)
        held: list[int] = []
        self.addCleanup(lambda: [os.close(fd) for fd in held])
        while True:
            fd = os.open(os.devnull, os.O_RDONLY)
            held.append(fd)
            if fd >= 1024:
                break
        handle = bash("echo hi; sleep 30 & true")
        self.addCleanup(handle.kill, signal.SIGKILL)
        result = await asyncio.wait_for(handle, timeout=5)
        self.assertEqual(result.exit_code, 0)
        self.assertIn("hi", result.output)

    async def test_awaits_do_not_hold_executor_threads(self):
        loop = asyncio.get_running_loop()
        executor = ThreadPoolExecutor(max_workers=1)
        loop.set_default_executor(executor)
        tasks = [asyncio.ensure_future(bash("sleep 0.5")._wait()) for _ in range(3)]
        await asyncio.sleep(0.1)
        # Old executor-parked waits would deadlock this 1-thread pool.
        value = await asyncio.wait_for(loop.run_in_executor(None, lambda: 42), timeout=0.3)
        self.assertEqual(value, 42)
        results = await asyncio.gather(*tasks)
        self.assertTrue(all(r.exit_code == 0 for r in results))

    def test_buffer_tail_retention_is_exact(self):
        buffer = bash_module._BoundedBuffer()
        buffer.write(b"x" * bash_module._HEAD_CAP)
        buffer.write(b"a" * bash_module._TAIL_CAP)
        buffer.write(b"b" * 1000)
        self.assertEqual(buffer._tail_size, bash_module._TAIL_CAP)
        text = buffer.text()
        self.assertTrue(text.endswith("b" * 1000))
        self.assertIn("a" * 1000 + "b" * 1000, text)

    async def test_running_reflects_group_liveness(self):
        handle = bash("echo fg; sleep 30 &")
        result = await asyncio.wait_for(handle, timeout=5)
        self.assertEqual(result.exit_code, 0)
        # The foreground result is in, but the group still anchors `sleep 30 &`.
        self.assertIsNotNone(handle.poll())
        self.assertTrue(handle.running)
        handle.kill(signal.SIGKILL)
        for _ in range(100):
            if not handle.running:
                break
            await asyncio.sleep(0.05)
        self.assertFalse(handle.running)

    def test_gate_eof_without_journal_prevents_command_execution(self):
        # A kernel SIGKILL between Popen and journaling closes the parent socket;
        # the child's gate read must then EOF and exit before running the command.
        with tempfile.TemporaryDirectory() as tmp:
            marker = os.path.join(tmp, "ran")
            script = bash_module._status_script(f"touch {marker}", "a" * 32, "b" * 32)
            parent, child = socket.socketpair()
            proc = subprocess.Popen(
                [bash_module._shell(), "-c", script],
                stdin=child.fileno(),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            child.close()
            parent.close()  # simulate parent death before the gate byte
            proc.communicate(timeout=10)
            self.assertEqual(proc.returncode, 127)
            self.assertFalse(os.path.exists(marker))

    def test_status_socket_closed_when_wake_pipe_fails(self):
        acquired: list[int] = []
        closed: list[int] = []
        real_socketpair = socket.socketpair
        real_close = os.close

        def capturing_socketpair(*args, **kwargs):
            pair = real_socketpair(*args, **kwargs)
            acquired.extend((pair[0].fileno(), pair[1].fileno()))
            return pair

        def recording_close(fd):
            closed.append(fd)
            real_close(fd)

        with mock.patch.object(bash_module.socket, "socketpair", capturing_socketpair):
            with mock.patch.object(bash_module.os, "close", recording_close):
                with mock.patch.object(bash_module.os, "pipe", side_effect=OSError("boom")):
                    with self.assertRaises(OSError):
                        bash("echo never")
        self.assertEqual(len(acquired), 2)
        for fd in acquired:
            self.assertIn(fd, closed)

    async def test_cancelled_direct_await_kills_group(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = os.path.join(tmp, "marker")
            pids: list[int] = []
            original_init = bash_module.BashHandle.__init__

            def capturing_init(handle_self, command):
                original_init(handle_self, command)
                pids.append(handle_self._pid)

            async def run_oneshot():
                await bash(f"sleep 1.0 && touch {marker}")

            with mock.patch.object(bash_module.BashHandle, "__init__", capturing_init):
                task = asyncio.ensure_future(run_oneshot())
                await asyncio.sleep(0.3)
                task.cancel()
                with self.assertRaises(asyncio.CancelledError):
                    await task
            # The cancel path awaits confirmed group death before propagating.
            with self.assertRaises(ProcessLookupError):
                os.killpg(pids[0], 0)
            await asyncio.sleep(1.0)
            self.assertFalse(os.path.exists(marker))

    async def test_cancelled_direct_await_escalates_past_term_trap(self):
        # A TERM-trapping command must be group-KILLed before the cancel
        # resolves, so its later side effects never land.
        with tempfile.TemporaryDirectory() as tmp:
            marker = os.path.join(tmp, "marker")
            pids: list[int] = []
            original_init = bash_module.BashHandle.__init__

            def capturing_init(handle_self, command):
                original_init(handle_self, command)
                pids.append(handle_self._pid)

            async def run_oneshot():
                await bash(f"trap '' TERM; sleep 1.0; touch {marker}; sleep 30")

            with mock.patch.object(bash_module, "_CANCEL_TERM_GRACE", 0.2):
                with mock.patch.object(bash_module.BashHandle, "__init__", capturing_init):
                    task = asyncio.ensure_future(run_oneshot())
                    await asyncio.sleep(0.2)
                    task.cancel()
                    with self.assertRaises(asyncio.CancelledError):
                        await task
            with self.assertRaises(ProcessLookupError):
                os.killpg(pids[0], 0)
            await asyncio.sleep(1.2)
            self.assertFalse(os.path.exists(marker))

    async def test_background_handle_survives_cancel_of_creating_context(self):
        handles: list[bash_module.BashHandle] = []

        async def run_background():
            h = bash("sleep 30")
            handles.append(h)
            h.pid  # released as a deliberate background handle
            await asyncio.sleep(10)

        task = asyncio.ensure_future(run_background())
        await asyncio.sleep(0.3)
        task.cancel()
        with self.assertRaises(asyncio.CancelledError):
            await task
        handle = handles[0]
        try:
            os.killpg(handle._pid, 0)  # still alive
        finally:
            handle.kill(signal.SIGKILL)
        await asyncio.wait_for(handle, timeout=5)

    async def test_cancelling_await_on_released_handle_does_not_kill(self):
        handle = bash("sleep 30")
        self.assertTrue(handle.running)  # release as background handle

        async def wait_for_it():
            await handle

        task = asyncio.ensure_future(wait_for_it())
        await asyncio.sleep(0.3)
        task.cancel()
        with self.assertRaises(asyncio.CancelledError):
            await task
        try:
            os.killpg(handle._pid, 0)  # still alive
        finally:
            handle.kill(signal.SIGKILL)
        await asyncio.wait_for(handle, timeout=5)

    async def test_second_await_after_cancelled_oneshot_only_waits(self):
        handle = bash("echo done")
        # First await consumes the one-shot ownership; later awaits only wait.
        result = await handle
        self.assertEqual(result.exit_code, 0)
        self.assertTrue(handle._released)
        again = await handle
        self.assertEqual(again, result)

    async def test_second_cancel_during_cleanup_still_confirms_group_death(self):
        # Python 3.11: an await inside an except-CancelledError block of a
        # cancelled task is re-cancelled immediately; the shielded confirm task
        # must survive repeated cancels and the group must be dead on return.
        pids: list[int] = []
        original_init = bash_module.BashHandle.__init__

        def capturing_init(handle_self, command):
            original_init(handle_self, command)
            pids.append(handle_self._pid)

        async def run_oneshot():
            await bash("trap '' TERM; sleep 30")

        with mock.patch.object(bash_module, "_CANCEL_TERM_GRACE", 0.2):
            with mock.patch.object(bash_module.BashHandle, "__init__", capturing_init):
                task = asyncio.ensure_future(run_oneshot())
                await asyncio.sleep(0.2)
                task.cancel()
                await asyncio.sleep(0.05)
                task.cancel()  # lands inside the cleanup awaits
                await asyncio.sleep(0.05)
                task.cancel()
                with self.assertRaises(asyncio.CancelledError):
                    await task
        with self.assertRaises(ProcessLookupError):
            os.killpg(pids[0], 0)

    async def test_pump_delayed_past_old_quiescence_bound_captures_all_output(self):
        # The ordered sentinel must wait through a pump delay beyond the old 500 ms bound.
        original_write = bash_module._BoundedBuffer.write
        delayed_once = threading.Event()

        def delayed_write(buffer_self, chunk):
            if not delayed_once.is_set():
                delayed_once.set()
                time.sleep(0.7)
            original_write(buffer_self, chunk)

        with mock.patch.object(bash_module._BoundedBuffer, "write", delayed_write):
            result = await asyncio.wait_for(bash("printf delayed-output-complete"), timeout=5)
        self.assertEqual(result.exit_code, 0)
        self.assertEqual(result.output, "delayed-output-complete")

    async def test_completion_marker_split_across_reads_is_removed(self):
        with mock.patch.object(bash_module, "_READ_CHUNK", 7):
            result = await asyncio.wait_for(bash("printf exact-pre-fence-output"), timeout=5)
        self.assertEqual(result.output, "exact-pre-fence-output")

    async def test_slow_pump_does_not_lose_foreground_output(self):
        # Finalization waits for the pump to parse the ordered sentinel.
        original_pump = bash_module.BashHandle._pump

        def slow_pump(handle_self):
            time.sleep(0.3)
            original_pump(handle_self)

        with mock.patch.object(bash_module.BashHandle, "_pump", slow_pump):
            result = await asyncio.wait_for(bash("printf slow-pump-x"), timeout=5)
        self.assertEqual(result.exit_code, 0)
        self.assertIn("slow-pump-x", result.output)

    async def test_sentinel_like_output_and_echoed_wrapper_do_not_truncate(self):
        token = "0123456789abcdef" * 4
        raw_lookalike = "\x1eeukhe-complete:not-this-invocation\x1f"
        command = (
            "set -x\n"
            "printf '\\036eukhe-complete:not-this-invocation\\037'\n"
            "if [ -r /proc/$$/cmdline ]; then cat /proc/$$/cmdline; fi\n"
            "printf '\\nafter-sentinel-lookalike\\n'"
        )
        with mock.patch.object(bash_module.secrets, "token_hex", return_value=token):
            result = await asyncio.wait_for(bash(command), timeout=5)
        actual_marker = (
            bash_module._COMPLETION_PREFIX + token.encode() + bash_module._COMPLETION_SUFFIX
        )
        self.assertIn(raw_lookalike, result.output)
        self.assertIn("after-sentinel-lookalike", result.output)
        self.assertNotIn(actual_marker.decode(), result.output)

    async def test_user_alias_cannot_replace_completion_emitter(self):
        if os.path.basename(bash_module._shell()) != "bash":
            self.skipTest("bash alias expansion semantics")
        handle = bash(
            "shopt -s expand_aliases; alias command='printf alias-expanded'; sleep 30 &"
        )
        try:
            result = await asyncio.wait_for(handle, timeout=5)
            self.assertEqual(result.exit_code, 0)
            self.assertNotIn("alias-expanded", result.output)
        finally:
            handle.kill(signal.SIGKILL)
            await _poll_group_dead(handle.pid)

    async def test_user_function_cannot_replace_completion_emitter(self):
        # The backslash in `\command` defeats alias expansion only: a shell
        # function named `command` would otherwise swallow both fence frames
        # and wedge the await behind the background job until shell death.
        handle = bash("command() { printf function-expanded; }; sleep 30 &")
        try:
            result = await asyncio.wait_for(handle, timeout=5)
            self.assertEqual(result.exit_code, 0)
            self.assertNotIn("function-expanded", result.output)
        finally:
            handle.kill(signal.SIGKILL)
            await _poll_group_dead(handle.pid)

    async def test_shell_killed_before_sentinel_finalizes_from_exit(self):
        result = await asyncio.wait_for(
            bash("printf output-before-shell-kill; kill -KILL $$"), timeout=5
        )
        self.assertEqual(result.exit_code, -signal.SIGKILL)
        self.assertIn("output-before-shell-kill", result.output)

    async def test_relative_bash_shell_override_rejected(self):
        with mock.patch.dict(os.environ, {"EUKHE_BASH_SHELL": "bash"}):
            with self.assertRaises(ValueError):
                bash("echo hi")

    def test_darwin_start_id_uses_absolute_ps(self):
        completed = mock.Mock(stdout="Mon Jan  1 00:00:00 2026\n")
        with mock.patch.object(bash_module.sys, "platform", "darwin"):
            with mock.patch("builtins.open", side_effect=OSError):
                with mock.patch.object(bash_module.subprocess, "run", return_value=completed) as run:
                    self.assertEqual(
                        bash_module._process_start_id(1234), "ps:Mon Jan  1 00:00:00 2026"
                    )
        self.assertEqual(run.call_args.args[0][0], "/bin/ps")

    async def test_undelivered_kill_leaves_journal_record_active(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                handle = bash("sleep 30")
                try:
                    records = await _poll_journal(journal, count=1)
                    self.assertTrue(records[-1]["active"])
                    with mock.patch.object(bash_module, "_signal_group", return_value=False):
                        bash_module._kill_live_handles()
                    await asyncio.sleep(0.2)  # give any (wrong) inactive write time to land
                    records = await _poll_journal(journal, count=1)
                    self.assertEqual(len(records), 1)
                    self.assertTrue(records[-1]["active"])
                finally:
                    handle.kill(signal.SIGKILL)
                    await asyncio.wait_for(handle, timeout=5)

    async def test_signal_group_reports_delivery(self):
        with mock.patch.object(bash_module.os, "killpg", side_effect=ProcessLookupError):
            self.assertTrue(bash_module._signal_group(1234567, signal.SIGKILL))
        with mock.patch.object(bash_module.os, "killpg", side_effect=PermissionError):
            self.assertFalse(bash_module._signal_group(1234567, signal.SIGKILL))
        with mock.patch.object(bash_module.os, "killpg", side_effect=OSError):
            self.assertFalse(bash_module._signal_group(1234567, signal.SIGKILL))

    async def test_journal_configured_but_unwritable_kills_child_and_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = os.path.join(tmp, "marker")
            pids: list[int] = []
            real_popen = subprocess.Popen

            def capturing_popen(*args, **kwargs):
                proc = real_popen(*args, **kwargs)
                pids.append(proc.pid)
                return proc

            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": tmp,  # a directory: open fails
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                with mock.patch.object(bash_module.subprocess, "Popen", capturing_popen):
                    with self.assertRaises(RuntimeError):
                        bash(f"touch {marker}")
            await _poll_group_dead(pids[0])
            await asyncio.sleep(0.2)
            self.assertFalse(os.path.exists(marker))
            with bash_module._live_lock:
                self.assertFalse(bash_module._live_handles)

    async def test_journal_bad_owner_pid_rejects(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": "notanint",
                },
            ):
                with self.assertRaises(RuntimeError):
                    bash("echo hi")

    async def test_missing_start_id_rejects_when_configured(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                with mock.patch.object(bash_module, "_process_start_id", return_value=None):
                    with self.assertRaises(RuntimeError):
                        bash("sleep 30")

    async def test_journal_short_write_rejects_when_configured(self):
        # A partial os.write would leave a truncated JSON line the host
        # discards; enrollment must treat it as failure.
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")

            def short_write(fd, data):
                return 0  # no progress

            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                with mock.patch.object(bash_module.os, "write", short_write):
                    self.assertFalse(bash_module._record_journal(os.getpid(), active=False))

    async def test_journal_partial_writes_complete_the_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal = os.path.join(tmp, "journal.jsonl")
            real_write = os.write

            def partial_write(fd, data):
                # One byte at a time: the loop must still write the full record.
                return real_write(fd, bytes(data)[:1])

            with mock.patch.dict(
                os.environ,
                {
                    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL": journal,
                    "EUKHE_KERNEL_OWNER_PID": str(os.getpid()),
                },
            ):
                with mock.patch.object(bash_module.os, "write", partial_write):
                    self.assertTrue(bash_module._record_journal(os.getpid(), active=False))
            with open(journal) as f:
                record = json.loads(f.read())
            self.assertEqual(record["pid"], os.getpid())
            self.assertFalse(record["active"])

    async def test_unconfigured_journal_stays_permissive(self):
        # Permissiveness is about configuration, not start-id availability.
        with mock.patch.object(bash_module, "_process_start_id", return_value=None):
            result = await bash("echo ok")
        self.assertEqual(result.exit_code, 0)
        self.assertIn("ok", result.output)


async def _poll_group_dead(pgid: int, timeout: float = 5.0) -> None:
    deadline = asyncio.get_running_loop().time() + timeout
    while asyncio.get_running_loop().time() < deadline:
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            return
        except PermissionError:
            pass  # transient teardown state on macOS
        await asyncio.sleep(0.05)
    raise AssertionError(f"process group {pgid} still alive after {timeout}s")


async def _poll_journal(path: str, count: int, timeout: float = 2.0) -> list[dict]:
    deadline = asyncio.get_running_loop().time() + timeout
    records: list[dict] = []
    while asyncio.get_running_loop().time() < deadline:
        with open(path) as f:
            records = [json.loads(line) for line in f if line.strip()]
        if len(records) >= count:
            return records
        await asyncio.sleep(0.05)
    return records


if __name__ == "__main__":
    unittest.main()
