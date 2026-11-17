#!/usr/bin/env python3
"""tmux verifier for the eukhe-tui lane.

Renders a captured real agent session (~/.eukhe/sessions) in the eukhe-tui
agent view inside an 80x24 tmux session, captures the pane, and asserts the
structural contract of the TS product's interactive view:
  - transcript content present (assistant markdown text, tool headers)
  - a full-width "-" separator above the editor (dynamic-border parity)
  - ">" prompt prefix on the editor line (custom-editor promptPrefix)
  - model label footer
Then drives editor keys like a user (type, backspace, arrows, ctrl+o,
escape, ctrl+c) and asserts editor behavior parity:
  - typing appears at the prompt; backspace deletes
  - left/right/up/down move the cursor without exiting
  - ctrl+o (app.tools.expand) and escape do not exit or corrupt the pane
  - ctrl+c exits the app

Usage: python3 tests/tmux_replay.py [path-to-session.jsonl]
BIN: the replay binary (default target/debug/eukhe-tui-replay).
"""

from __future__ import annotations

import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

PANE_ROWS = 24
PANE_COLS = 80
PROMPT = r"^ ?> hello worl *$"


def first_assistant_words(session: Path) -> str:
    """The first two words of the session's first assistant text: proves the
    view renders this session, not any UI."""
    for line in session.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            entry = json.loads(line)
        except ValueError:
            continue
        message = entry.get("message", {}) if isinstance(entry, dict) else {}
        if message.get("role") == "assistant":
            for content in message.get("content", []):
                if content.get("type") == "text":
                    words = content["text"].split()
                    if len(words) >= 2:
                        return " ".join(words[:2])
    return ""


class Pane:
    def __init__(self, name: str) -> None:
        self.name = name
        self.fails = 0

    def tmux(self, *args: str) -> str:
        return subprocess.run(["tmux", *args], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True).stdout

    def keys(self, *keys: str) -> None:
        subprocess.run(["tmux", "send-keys", "-t", self.name, *keys])

    def capture(self) -> str:
        return self.tmux("capture-pane", "-t", self.name, "-p")

    def ok(self, what: str) -> None:
        print(f"ok: {what}", flush=True)

    def fail(self, what: str) -> None:
        print(f"FAIL: {what}", file=sys.stderr, flush=True)
        self.fails += 1

    def check(self, what: str, pattern: str) -> None:
        if re.search(pattern, self.capture(), re.MULTILINE):
            self.ok(what)
        else:
            self.fail(f"{what} (pattern: {pattern})")
            sys.stderr.write("".join(f"{line}\n" for line in self.capture().splitlines()[:10]))


def main() -> int:
    here = Path(__file__).resolve().parent
    binary = os.environ.get("BIN") or str(here / ".." / ".." / ".." / "target" / "debug" / "eukhe-tui-replay")
    if not (os.path.isfile(binary) and os.access(binary, os.X_OK)):
        print(f"FAIL: binary not found at {binary} (run cargo build -p eukhe-tui)", file=sys.stderr)
        return 1
    if len(sys.argv) > 1 and sys.argv[1]:
        session = Path(sys.argv[1])
    else:
        sessions = sorted(Path.home().glob(".eukhe/sessions/*.jsonl"), key=lambda path: path.stat().st_mtime, reverse=True)
        session = sessions[0] if sessions else None
    if session is None or not session.is_file():
        print("FAIL: no session file to replay", file=sys.stderr)
        return 1

    pane = Pane(f"patui-verify-{os.getpid()}")
    subprocess.run(["tmux", "new-session", "-d", "-s", pane.name, "-x", str(PANE_COLS), "-y", str(PANE_ROWS)])
    try:
        pane.keys(f"{binary} {shlex.quote(str(session))}", "Enter")
        time.sleep(3)

        # --- structural contract ---------------------------------------
        marker = first_assistant_words(session)
        if marker:
            pane.check("first assistant text from session on screen", re.escape(marker))
        pane.check("session rendered (markdown text or tool header present)", r"[A-Za-z]{4,}")
        pane.check("separator line above editor", r"^-{60,}$")
        pane.check("prompt prefix present", r"^ ?> ?$|^ ?> .+$")
        pane.check("model footer line", r"internal/|glm|z-ai|[a-z]+:.+ \(0%\)|[a-z]+-[0-9]")

        # --- interactive keys ------------------------------------------
        pane.keys("hello world")
        time.sleep(1)
        pane.check("typed text visible", r"^ ?> hello world *$")

        pane.keys("BSpace")
        time.sleep(0.5)
        pane.check("backspace deleted char", PROMPT)

        pane.keys("Left", "Left")
        time.sleep(0.5)
        cursor = pane.tmux("display-message", "-t", pane.name, "-p", "#{cursor_x},#{cursor_y}").strip()
        # "hello worl" (10 chars) + 2 left moves: logical col 8, visual col 8+3 prompt.
        if re.match(r"1[01],", cursor):
            pane.ok(f"cursor after left moves ({cursor})")
        else:
            pane.fail(f"cursor after left moves, got ({cursor})")

        pane.keys("Right", "Up", "Down")
        time.sleep(0.5)
        pane.check("arrow keys did not exit (prompt intact)", PROMPT)

        # ctrl+o = app.tools.expand (cycle detail): must not exit or crash.
        pane.keys("C-o")
        time.sleep(1)
        pane.check("ctrl+o did not exit", PROMPT)

        # escape cancels autocomplete/normal-mode actions: must not exit.
        pane.keys("Escape")
        time.sleep(1)
        pane.check("escape did not exit", PROMPT)

        # ctrl+c exits the app cleanly (pane returns to the shell process).
        pane.keys("C-c")
        time.sleep(2)
        command = pane.tmux("display-message", "-t", pane.name, "-p", "#{pane_current_command}").strip()
        if command in ("eukhe-tui-replay", ""):
            pane.fail(f"ctrl+c did not exit (pane: {command or 'gone'})")
        else:
            pane.ok(f"ctrl+c exited (pane now: {command})")
    finally:
        subprocess.run(["tmux", "kill-session", "-t", pane.name], stderr=subprocess.DEVNULL)

    if pane.fails == 0:
        print("ALL TMUX CHECKS PASSED")
        return 0
    print(f"{pane.fails} CHECK(S) FAILED", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
