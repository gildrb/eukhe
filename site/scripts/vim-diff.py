#!/usr/bin/env python3
"""Ground truth for the Bend editor: run the same keys in Gil's real Neovim and in the Bend core,
then diff the two screens cell for cell.

Real nvim runs in a pty with the user's config, on a temp folder holding the site's files
(dist/files.json, as `npx vp build` writes it), and draws into a pyte screen. The Bend side is
scripts/vim-screen.ts over the same files. Usage:

    python3 scripts/vim-diff.py                 # every scenario
    python3 scripts/vim-diff.py start ff        # some scenarios
    python3 scripts/vim-diff.py --show ff       # print both screens in full
    python3 scripts/vim-diff.py --keys '<Space>fg' --wait 2.5   # an ad hoc run

Picker scenarios (kind "float") compare the box geometry (every border cell), the title and the
prompt row; their item order may differ (fff ranks by frecency), so other rows are listed only.
"""
import argparse
import fcntl
import json
import os
import pty
import re
import select
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import termios
import time
from concurrent.futures import ThreadPoolExecutor

import pyte
import pyte.screens
import wcwidth


def cell_width(ch):
    """Cells a character takes: wcwidth's, but fff's goose (U+1FABF, Unicode 15) is wide even where
    wcwidth's tables predate it, as nvim draws it."""
    return 2 if ch == "\U0001FABF" else wcwidth.wcwidth(ch)


pyte.screens.wcwidth = cell_width

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Scenarios: name -> (steps, kind[, rows, cols]). A step is (keys, seconds to settle after them).
# Keys are Vim notation: characters, <CR>, <Esc>, <Space>, <C-d>, ...
SETUP_DOCS = (":e spec/memory/thread.bend<CR>", 0.4)
SCENARIOS = {
    "start": ([], "full"),
    "j20": ([("j" * 20, 0.5)], "full"),
    "G": ([("G", 0.5)], "full"),
    "gg": ([("G", 0.3), ("gg", 0.5)], "full"),
    "w": ([("w" * 12, 0.5)], "full"),
    "b": ([("G", 0.3), ("b" * 12, 0.5)], "full"),
    "e": ([("e" * 12, 0.5)], "full"),
    "para": ([("}}}", 0.5)], "full"),
    "C-d": ([("<C-d>", 0.5)], "full"),
    "C-d-u": ([("<C-d><C-d><C-d><C-u>", 0.5)], "full"),
    "search": ([("/memory<CR>n", 0.6)], "full"),
    "edit-docs": ([SETUP_DOCS], "full"),
    "oil-docs": ([SETUP_DOCS, ("-", 1.0)], "full"),
    "oil-up": ([SETUP_DOCS, ("-", 1.0), ("gg<CR>", 1.0)], "full"),
    "oil-back": ([SETUP_DOCS, ("-", 1.0), ("gg<CR>", 1.0), ("<CR>", 1.0), ("<CR>", 1.0)], "full"),
    "oil-alt": ([SETUP_DOCS, ("-", 1.0), ("<C-^>", 0.8)], "full"),
    "oil-root": ([("-", 1.0)], "full"),
    "ff": ([("<Space>ff", 4.0)], "float"),
    "ffq": ([("<Space>ff", 4.0), ("inst", 1.5)], "float"),
    "ff-small": ([("<Space>ff", 4.0)], "float", 30, 100),
    "fg": ([("<Space>fg", 4.0)], "float"),
    "fgq": ([("<Space>fg", 4.0), ("memory", 1.5)], "float"),
    "fb": ([("<Space>fb", 4.0)], "float"),
    "bl": ([("<Space>/", 4.0)], "float"),
}

KEYS = {
    "<Space>": " ", "<CR>": "\r", "<Esc>": "\x1b", "<BS>": "\x7f", "<Tab>": "\t",
    "<S-Tab>": "\x1b[Z", "<Up>": "\x1b[A", "<Down>": "\x1b[B", "<Right>": "\x1b[C",
    "<Left>": "\x1b[D", "<lt>": "<", "<C-^>": "\x1e",
}
BOX = set("┌┐└┘├┤┬┴┼│─╭╮╰╯")


def tokens(keys):
    """Vim notation split into keys."""
    out, i = [], 0
    while i < len(keys):
        if keys[i] == "<":
            j = keys.find(">", i)
            if j > 0:
                out.append(keys[i : j + 1])
                i = j + 1
                continue
        out.append(keys[i])
        i += 1
    return out


def key_bytes(t):
    if t in KEYS:
        return KEYS[t]
    if t.startswith("<C-") and len(t) == 5:
        return chr(ord(t[3].upper()) & 0x1F)
    return t


def bend_name(t):
    return "<Space>" if t == " " else t


class Screen(pyte.Screen):
    """pyte's screen with REP (CSI b), which nvim uses for runs of one character."""

    last = " "

    def draw(self, data):
        if data:
            self.last = data[-1]
        super().draw(data)

    def repeat_last(self, n=1, *args, **kwargs):
        super().draw(self.last * max(n, 1))


class Stream(pyte.ByteStream):
    csi = dict(pyte.ByteStream.csi, b="repeat_last")


STRING_SEQ = re.compile(rb"\x1b[P_^][^\x1b]*(?:\x1b\\|$)")


class Feed:
    """Bytes into a pyte stream, less DCS/APC/PM strings (nvim's XTGETTCAP queries), which pyte
    would print as text."""

    def __init__(self, stream):
        self.stream = stream
        self.held = b""

    def __call__(self, data):
        data = self.held + data
        self.held = b""
        m = re.search(rb"\x1b[P_^][^\x1b]*\Z|\x1b\Z", data)
        if m:
            self.held = data[m.start() :]
            data = data[: m.start()]
        self.stream.feed(STRING_SEQ.sub(b"", data))


def make_tree(files):
    tmp = tempfile.mkdtemp(prefix="vimdiff-")
    for f in files:
        p = os.path.join(tmp, f["path"])
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as out:
            out.write("\n".join(f["lines"]) + "\n")
    return tmp


def nvim(steps, rows, cols, cwd, root, wait0=2.5):
    """The screen of real nvim after steps: display rows and the cursor."""
    state = tempfile.mkdtemp(dir=root)
    pid, fd = pty.fork()
    if pid == 0:
        fcntl.ioctl(0, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
        os.chdir(cwd)
        os.environ["TERM"] = "xterm-256color"
        # shada, undo files, sessions and fff's frecency stay out of the user's own state
        os.environ["XDG_STATE_HOME"] = os.path.join(state, "state")
        os.environ["XDG_CACHE_HOME"] = os.path.join(state, "cache")
        os.environ["NVIM_LOG_FILE"] = os.path.join(state, "nvim.log")
        os.execvp("nvim", ["nvim", "index.md"])
    scr = Screen(cols, rows)
    feed = Feed(Stream(scr))
    scr.write_process_input = lambda data: os.write(fd, data.encode())

    def pump(t):
        end = time.time() + t
        while time.time() < end:
            r, _, _ = select.select([fd], [], [], 0.02)
            if r:
                try:
                    feed(os.read(fd, 65536))
                except OSError:
                    return

    pump(wait0)
    for keys, wait in steps:
        for t in tokens(keys):
            os.write(fd, key_bytes(t).encode())
            pump(0.06)
        pump(wait)
    out = {"lines": list(scr.display), "cur": [scr.cursor.y, scr.cursor.x]}
    os.kill(pid, signal.SIGKILL)
    os.waitpid(pid, 0)
    os.close(fd)
    return out


def bend(files, rows, cols, scenarios):
    job = {
        "files": files,
        "rows": rows,
        "cols": cols,
        "scenarios": [
            {"name": n, "keys": [bend_name(t) for keys, _ in steps for t in tokens(keys)]}
            for n, steps in scenarios
        ],
    }
    out = subprocess.run(
        ["node", os.path.join(ROOT, "scripts/vim-screen.ts")],
        input=json.dumps(job),
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(out.stdout)


def cells(row):
    out = []
    for ch in row:
        out.append(ch)
        if cell_width(ch) == 2:
            out.append("")
    return out


def rejustify(row, cols, old, new):
    """The statusline with old replaced by new, its ruler kept at the right edge."""
    m = re.match(r"^(.*?)\s*(\S+ ?)\s*$", row)
    if not m or (old not in row and not old.startswith("term")):
        return row
    left = re.sub(old, new, m.group(1)) if old.startswith("term") else m.group(1).replace(old, new)
    right = m.group(2)
    return left + " " * max(1, cols - len(left) - len(right)) + right


def normalize(screen, rows, cols, tmp):
    lines = list(screen["lines"])
    s = lines[rows - 2]
    if tmp in s:
        s = rejustify(s, cols, tmp, "")
    if "term://" in s:
        s = rejustify(s, cols, r"term://\S*//\d+:\S+", "term:////1:/bin/sh")
    lines[rows - 2] = s
    return {"lines": lines, "cur": screen["cur"]}


def box_mask(lines):
    return ["".join(c if c in BOX else "." for c in cells(r)) for r in lines]


def compare(name, kind, real, ours, show):
    diff = [i for i, (a, b) in enumerate(zip(real["lines"], ours["lines"])) if a != b]
    cur_ok = real["cur"] == ours["cur"]
    verdict = []
    if kind == "full":
        verdict.append("OK" if not diff and cur_ok else f"DIFF {len(diff)} rows" + ("" if cur_ok else " +cursor"))
    else:
        geo = box_mask(real["lines"]) == box_mask(ours["lines"])
        rows_with_box = [i for i, r in enumerate(real["lines"]) if any(c in BOX for c in r)]
        prompt = rows_with_box[1] if len(rows_with_box) > 1 else None
        prompt_ok = prompt is not None and real["lines"][prompt] == ours["lines"][prompt]
        top_ok = bool(rows_with_box) and real["lines"][rows_with_box[0]] == ours["lines"][rows_with_box[0]]
        verdict.append(
            f"geometry {'ok' if geo else 'DIFF'}, title row {'ok' if top_ok else 'DIFF'}, "
            f"prompt row {'ok' if prompt_ok else 'DIFF'}, cursor {'ok' if cur_ok else 'DIFF'}, "
            f"{len(diff)} rows differ"
        )
    print(f"== {name}: {verdict[0]}   cursor nvim={real['cur']} bend={ours['cur']}")
    if show:
        for i, (a, b) in enumerate(zip(real["lines"], ours["lines"])):
            print(f"{i:2} {'=' if a == b else '!'} N|{a}|")
            if a != b:
                print(f"     B|{b}|")
    else:
        for i in diff:
            print(f"  {i:2} nvim|{real['lines'][i]}|")
            print(f"     bend|{ours['lines'][i]}|")
    return not diff and cur_ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("names", nargs="*")
    ap.add_argument("--show", action="store_true", help="print both screens in full")
    ap.add_argument("--keys", help="an ad hoc scenario")
    ap.add_argument("--wait", type=float, default=1.0)
    ap.add_argument("--rows", type=int, default=37)
    ap.add_argument("--cols", type=int, default=150)
    ap.add_argument("--files", default=os.path.join(ROOT, "dist/files.json"))
    ap.add_argument("--bend-only", action="store_true")
    args = ap.parse_args()

    with open(args.files) as f:
        files = [{"path": x["path"], "lines": x["lines"]} for x in json.load(f)]
    if args.keys is not None:
        scenarios = {"adhoc": ([(args.keys, args.wait)], "full", args.rows, args.cols)}
    else:
        names = args.names or list(SCENARIOS)
        scenarios = {n: SCENARIOS[n] for n in names}

    def size(sc):
        return (sc[2], sc[3]) if len(sc) > 2 else (args.rows, args.cols)

    groups = {}
    for n, sc in scenarios.items():
        groups.setdefault(size(sc), []).append((n, sc[0]))
    ours = {}
    for (rows, cols), scs in groups.items():
        ours.update(bend(files, rows, cols, scs))
    if args.bend_only:
        for n, sc in scenarios.items():
            o = ours[n]
            print(f"== {n} cursor={o['cur']} max key ms={max(o['ms'], default=0):.2f}")
            for i, r in enumerate(o["lines"]):
                print(f"{i:2}|{r}|")
        return

    tmp = make_tree(files)
    state = tempfile.mkdtemp(prefix="vimstate-")
    try:
        with ThreadPoolExecutor(max_workers=4) as pool:
            jobs = {
                n: pool.submit(nvim, sc[0], *size(sc), tmp, state) for n, sc in scenarios.items()
            }
            real = {n: j.result() for n, j in jobs.items()}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        shutil.rmtree(state, ignore_errors=True)

    summary = []
    for n, sc in scenarios.items():
        rows, cols = size(sc)
        r = normalize(real[n], rows, cols, tmp)
        ok = compare(n, sc[1], r, ours[n], args.show)
        slow = max(ours[n]["ms"], default=0)
        summary.append((n, sc[1], ok, slow))
    print("\nscenario      kind   exact  max key ms")
    for n, kind, ok, slow in summary:
        print(f"{n:13} {kind:6} {'yes' if ok else 'no':6} {slow:.2f}")


if __name__ == "__main__":
    main()
