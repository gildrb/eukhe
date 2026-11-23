#!/usr/bin/env python3
"""ram_map.py: resident memory of every process eukhe starts, per scenario.

    ram_map.py [--eukhe BIN] [--kernel-python PY] [--runs N] [--scenarios a,b]
               [--fixture DIR] [--json FILE]

Linux only: RSS and PSS come from /proc/<pid>/smaps_rollup. Each run starts
the supervisor (`eukhe --mode daemon`, as the client launches it) in a fresh
HOME and TMPDIR with its own socket and faux-scripted sessions (no network,
no auth), waits until the summed RSS settles, and samples every process of
that HOME: supervisor, session and subagent workers, kernels, the `eukhe`
TUI in a pty, `eukhe -p`. The table shows, per scenario and process role,
the process count and the median over N runs (default 3) of the
per-process mean RSS, PSS, anonymous PSS and file-backed PSS (MB); `total
PSS` sums every process of the scenario. File-backed PSS splits a page
among every process mapping it, other users of the same files included
(the kernel's libpython): compare passes on anonymous PSS and total PSS.

Scenarios (all by default):
- idle-daemon: the supervisor alone.
- idle-session: one created session, no prompt.
- turns-50: one session after 50 turns, each a python or read tool call
  and a ~1.5 KB answer.
- sessions-5: five sessions, one turn each.
- python-cell: one session after one python cell.
- subagents: one session whose python cell spawned two subagents
  (`rlm.spawn`), each settled and resident.
- tui-2000: the TUI (160x50 pty) attached to a session of 2,000 messages
  (500 tool turns, built once into --fixture, default a temp dir; reuse a
  fixture across passes only for one binary's session format).
- print: `eukhe -p` mid-run (its faux answer is held 8 s).

--eukhe is the binary (default target/release/eukhe); --kernel-python the
kernel interpreter (default $EUKHE_KERNEL_PYTHON), a venv of crates/rlm/ and
the Python skills, as the real-kernel tests build it:

    UV_PROJECT_ENVIRONMENT=$V uv sync --locked --group kernel --group dev \\
        --python 3.14 --project crates/rlm
    uv pip install --python $V/bin/python --no-deps --no-build-isolation \\
        $(for s in crates/skills/*/pyproject.toml; do echo --editable "${s%/*}"; done)
"""
import argparse
import fcntl
import json
import os
import pty
import shutil
import signal
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import termios
import threading
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
PROTOCOL = {"name": "eukhe.daemon", "version": 7}
FIXTURE_TURNS = 500
KB = 1024


# ---- /proc sampling ---------------------------------------------------------

def rollup(pid):
    """smaps_rollup fields of `pid` in kB, or None once it is gone."""
    try:
        with open(f"/proc/{pid}/smaps_rollup") as f:
            lines = f.read().splitlines()
    except OSError:
        return None
    fields = {}
    for line in lines[1:]:
        key, _, rest = line.partition(":")
        parts = rest.split()
        if parts and parts[0].isdigit():
            fields[key] = int(parts[0])
    return fields


def parents():
    """pid -> ppid of every process."""
    table = {}
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat") as f:
                stat = f.read()
        except OSError:
            continue
        table[int(entry)] = int(stat[stat.rindex(")") + 2:].split()[1])
    return table


def tree(roots):
    """`roots` and every live descendant."""
    table = parents()
    found = [pid for pid in roots if pid in table]
    frontier = list(found)
    while frontier:
        parent = frontier.pop()
        children = [pid for pid, ppid in table.items() if ppid == parent]
        found.extend(children)
        frontier.extend(children)
    return found


def cmdline(pid):
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as f:
            return [a.decode(errors="replace") for a in f.read().split(b"\0") if a]
    except OSError:
        return []


def role(pid, labels):
    """The role name of `pid`: `labels` (pid -> role) first, then argv."""
    if pid in labels:
        return labels[pid]
    argv = cmdline(pid)
    if not argv:
        return None
    exe = os.path.basename(argv[0])
    if exe.startswith("eukhe"):
        if argv[1:2] in (["worker"], ["tiny-worker"]):
            return argv[1]
        if "--mode" in argv and argv[argv.index("--mode") + 1:][:1] == ["daemon"]:
            return "daemon"
        return f"eukhe {' '.join(argv[1:3])}"
    if exe.startswith("python"):
        return f"kernel ({role(parents().get(pid), labels)})"
    return f"other:{exe}"


def sample(roots, labels):
    """{role: [rollup, ...]} over the process trees of `roots`."""
    out = {}
    for pid in sorted(set(tree(roots))):
        name = role(pid, labels)
        fields = rollup(pid)
        if name and fields:
            out.setdefault(name, []).append(fields)
    return out


def settle(roots, labels, expect=(), timeout=60.0):
    """Wait until every role in `expect` is present and the summed RSS of the
    trees of `roots()` moves under 1 % across three 0.5 s samples; return the
    sample."""
    deadline = time.monotonic() + timeout
    history = []
    while True:
        snap = sample(roots(), labels)
        total = sum(f["Rss"] for fields in snap.values() for f in fields)
        present = all(name in snap for name in expect)
        history = (history + [total])[-3:] if present else []
        if len(history) == 3 and max(history) - min(history) <= max(history) * 0.01:
            return snap
        if time.monotonic() > deadline:
            missing = [name for name in expect if name not in snap]
            if missing:
                raise RuntimeError(f"never appeared: {missing}; seen {sorted(snap)}")
            return snap
        time.sleep(0.5)


# ---- the daemon wire --------------------------------------------------------

class Client:
    """JSONL supervisor client: command envelopes, id-matched responses."""

    def __init__(self, path):
        # eukhe binds its sockets in the abstract namespace on Linux.
        self.sock = socket.socket(socket.AF_UNIX)
        self.sock.connect("\0" + path)
        self.file = self.sock.makefile("rb")
        self.next_id = 0
        hello = json.loads(self.file.readline())
        if hello.get("type") != "daemon_hello":
            raise RuntimeError(f"no daemon hello: {hello}")

    def call(self, command, timeout=300.0):
        self.next_id += 1
        ident = f"r{self.next_id}"
        envelope = {"type": "command", "id": ident, "protocol": PROTOCOL, "command": command}
        self.sock.sendall((json.dumps(envelope) + "\n").encode())
        self.sock.settimeout(timeout)
        while True:
            line = self.file.readline()
            if not line:
                raise RuntimeError(f"daemon closed the socket during {command['type']}")
            message = json.loads(line)
            if message.get("id") == ident:
                if not message.get("success"):
                    raise RuntimeError(f"{command['type']} failed: {message}")
                return message.get("data")

    def close(self):
        self.file.close()
        self.sock.close()


class Home:
    """An isolated HOME/TMPDIR with a supervisor on its own socket."""

    def __init__(self, path, eukhe, kernel_python):
        self.path = path
        self.eukhe = eukhe
        self.agent_dir = os.path.join(path, ".eukhe")
        self.cwd = os.path.join(path, "project")
        self.socket = os.path.join(path, "d.sock")
        for d in (self.agent_dir, self.cwd, os.path.join(path, "tmp")):
            os.makedirs(d, exist_ok=True)
        self.env = {
            "HOME": path, "TMPDIR": os.path.join(path, "tmp"), "USER": os.environ.get("USER", ""),
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LANG": "C.UTF-8",
            "TERM": "xterm-256color", "EUKHE_DAEMON_SOCKET": self.socket,
            "EUKHE_KERNEL_PYTHON": kernel_python,
        }
        self.daemon = None
        self.clients = []
        self.labels = {}

    def start(self):
        log = open(os.path.join(self.path, "daemon.log"), "ab")
        self.daemon = subprocess.Popen(
            [self.eukhe, "--mode", "daemon", "--daemon-socket", self.socket],
            env=self.env, cwd=self.cwd, stdin=subprocess.DEVNULL, stdout=log, stderr=log,
            start_new_session=True)
        deadline = time.monotonic() + 30
        while True:
            try:
                self.client = Client(self.socket)
                return
            except OSError:
                if self.daemon.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError(f"the supervisor never listened ({self.path}/daemon.log)")
                time.sleep(0.05)

    def script(self, name, responses):
        """A faux script file; its window is wide enough that no turn compacts."""
        path = os.path.join(self.path, f"{name}.json")
        with open(path, "w") as f:
            json.dump({"engine": "faux", "modelId": "faux-1", "contextWindow": 100_000_000,
                       "responses": responses}, f)
        return path

    def create(self, name, responses, child=None):
        config = {"cwd": self.cwd, "sessionDir": os.path.join(self.agent_dir, "sessions"),
                  "script": self.script(name, responses)}
        if child is not None:
            config["childScript"] = self.script(f"{name}-child", child)
        data = self.client.call({"type": "create", "name": name, "config": config})
        return data.get("activeSessionId") or data["id"]

    def turn(self, session, message):
        self.client.call({"type": "prompt", "activeSessionId": session, "message": message})
        self.client.call({"type": "wait_for_idle", "activeSessionId": session})

    def worker_pids(self):
        """activeSessionId -> worker pid, from the worker descriptors."""
        out = {}
        base = os.path.join(self.agent_dir, "daemon-workers")
        for instance in os.listdir(base) if os.path.isdir(base) else ():
            for name in os.listdir(os.path.join(base, instance)):
                if not name.endswith(".json"):
                    continue
                try:
                    with open(os.path.join(base, instance, name)) as f:
                        pid = json.load(f).get("pid")
                except (OSError, ValueError):
                    continue
                if pid:
                    out[name[:-5]] = pid
        return out

    def label_workers(self, sessions):
        """Workers of `sessions` read as `worker`, every other as `subagent worker`."""
        for session, pid in self.worker_pids().items():
            self.labels[pid] = "worker" if session in sessions else "subagent worker"

    def pids(self):
        """Every live process of this home: the supervisor and clients started
        here, their descendants, and any process whose HOME is this home (a
        supervisor a client launched detached)."""
        roots = [p.pid for p in [self.daemon, *self.clients] if p is not None]
        roots += [pid for pid in parents() if env_home(pid) == self.path]
        return roots

    def measure(self, expect=()):
        return settle(self.pids, self.labels, expect)

    def stop(self):
        for proc in self.clients:
            kill_group(proc)
        if self.daemon:
            if hasattr(self, "client"):
                self.client.close()
            kill_group(self.daemon)
        # Workers and kernels leave the supervisor's group: stop any left.
        for pid in tree([pid for pid in parents() if env_home(pid) == self.path]):
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass


def env_home(pid):
    try:
        with open(f"/proc/{pid}/environ", "rb") as f:
            for item in f.read().split(b"\0"):
                if item.startswith(b"HOME="):
                    return item[5:].decode(errors="replace")
    except OSError:
        return None
    return None


def kill_group(proc):
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(10)
    except (OSError, subprocess.TimeoutExpired):
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            pass
        proc.wait()


# ---- faux turns -------------------------------------------------------------

def tool_turn(i, path):
    """Turn i: a python cell or a read of `path`, then a ~1.5 KB answer."""
    if i % 2:
        call = {"type": "toolCall", "id": f"call_{i}", "name": "read", "arguments": {"path": path}}
    else:
        code = f"rows = [f'row {{n}}: ' + 'x' * 60 for n in range(50)]\nprint('\\n'.join(rows))  # {i}"
        call = {"type": "toolCall", "id": f"call_{i}", "name": "python", "arguments": {"code": code}}
    answer = f"Turn {i}: " + ("The tool output shows the rows as expected. " * 35)
    return [{"content": [{"type": "text", "text": f"Checking ({i})."}, call]}, {"text": answer}]


def sample_file(home):
    path = os.path.join(home.cwd, "notes.txt")
    with open(path, "w") as f:
        f.write("".join(f"line {n}: the quick brown fox jumps over the lazy dog\n"
                        for n in range(150)))
    return path


def run_turns(home, name, count):
    path = sample_file(home)
    responses = [step for i in range(count) for step in tool_turn(i, path)]
    session = home.create(name, responses)
    for i in range(count):
        home.turn(session, f"turn {i}: check the notes")
    return session


# ---- scenarios --------------------------------------------------------------

def idle_daemon(home, _args):
    return home.measure(["daemon"])


def idle_session(home, _args):
    session = home.create("s", [{"text": "unused"}])
    home.label_workers({session})
    return home.measure(["daemon", "worker"])


def turns_50(home, _args):
    session = run_turns(home, "s", 50)
    home.label_workers({session})
    return home.measure(["worker", "kernel (worker)"])


def sessions_5(home, _args):
    sessions = set()
    for n in range(5):
        session = home.create(f"s{n}", [{"text": f"session {n} answered"}])
        home.turn(session, "hello")
        sessions.add(session)
    home.label_workers(sessions)
    return home.measure(["worker"])


def python_cell(home, _args):
    code = ("import os, re, json, pathlib\n"
            "files = sorted(p.name for p in pathlib.Path('.').iterdir())\n"
            "print(json.dumps({'files': files, 'cwd': os.getcwd()}))")
    session = home.create("s", [
        {"content": [{"type": "toolCall", "id": "call_1", "name": "python",
                      "arguments": {"code": code}}]},
        {"text": "done"},
    ])
    home.turn(session, "list the files")
    home.label_workers({session})
    return home.measure(["worker", "kernel (worker)"])


def subagents(home, _args):
    code = ("a = await rlm.spawn('task a', name='kid-a')\n"
            "b = await rlm.spawn('task b', name='kid-b')\n"
            "for h in (a, b):\n"
            "    print([r.status for r in await rlm.collect(h, timeout_ms=120000)])")
    session = home.create("s", [
        {"content": [{"type": "toolCall", "id": "call_1", "name": "python",
                      "arguments": {"code": code}}]},
        {"text": "both kids answered"},
    ], child=[{"text": "kid done"}])
    home.turn(session, "spawn two kids")
    home.label_workers({session})
    return home.measure(["worker", "subagent worker"])


def build_fixture(args):
    """A home holding one session of FIXTURE_TURNS tool turns; its id."""
    marker = os.path.join(args.fixture, "session-id")
    if os.path.exists(marker):
        with open(marker) as f:
            return f.read().strip()
    print(f"building the {FIXTURE_TURNS}-turn fixture in {args.fixture}", file=sys.stderr)
    shutil.rmtree(args.fixture, ignore_errors=True)
    home = Home(args.fixture, args.eukhe, args.kernel_python)
    try:
        home.start()
        session = run_turns(home, "big", FIXTURE_TURNS)
        count = len(home.client.call({"type": "get_messages", "activeSessionId": session})["messages"])
        if count < 4 * FIXTURE_TURNS:
            raise RuntimeError(f"the fixture holds {count} messages, not {4 * FIXTURE_TURNS}")
        state = home.client.call({"type": "get_state", "activeSessionId": session})
        session_id = state.get("sessionId") or session
    finally:
        home.stop()
    with open(marker, "w") as f:
        f.write(session_id)
    return session_id


def drain(fd):
    while True:
        try:
            if not os.read(fd, 65536):
                return
        except OSError:
            return


def tui_2000(home, args):
    session_id = build_fixture(args)
    # The fixture home is the run's home: reuse its sessions under a fresh supervisor.
    master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 50, 160, 0, 0))
    tui = subprocess.Popen(
        [args.eukhe, "--daemon-socket", home.socket, "--resume", session_id],
        env=home.env, cwd=home.cwd, stdin=slave, stdout=slave, stderr=slave,
        start_new_session=True)
    os.close(slave)
    threading.Thread(target=drain, args=(master,), daemon=True).start()
    home.clients.append(tui)
    home.labels[tui.pid] = "tui"
    deadline = time.monotonic() + 60
    while not home.worker_pids() and time.monotonic() < deadline:
        time.sleep(0.2)
    home.label_workers(set(home.worker_pids()))
    return home.measure(["tui", "worker"])


def print_mode(home, args):
    script = {"engine": "faux", "modelId": "faux-1",
              "responses": [{"text": "printed", "delayMs": 8000}]}
    env = dict(home.env, EUKHE_FAUX_SCRIPT=json.dumps(script))
    proc = subprocess.Popen([args.eukhe, "-p", "say something"],
                            env=env, cwd=home.cwd, stdin=subprocess.DEVNULL,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                            start_new_session=True)
    home.clients.append(proc)
    home.labels[proc.pid] = "print"
    snap = home.measure(["print"])
    if proc.wait(60):
        raise RuntimeError(f"eukhe -p failed with {proc.returncode}")
    return snap


SCENARIOS = {
    "idle-daemon": idle_daemon,
    "idle-session": idle_session,
    "turns-50": turns_50,
    "sessions-5": sessions_5,
    "python-cell": python_cell,
    "subagents": subagents,
    "tui-2000": tui_2000,
    "print": print_mode,
}


# ---- report -----------------------------------------------------------------

def summarize(snap):
    """{role: (count, rss, pss, pss_anon, pss_file)} in MB, per-process means."""
    out = {}
    for name, fields in snap.items():
        n = len(fields)
        mean = lambda key: sum(f.get(key, 0) for f in fields) / n / KB  # noqa: E731
        out[name] = (n, mean("Rss"), mean("Pss"), mean("Pss_Anon"), mean("Pss_File"))
    return out


def table(results):
    rows = [f"| scenario | process | n | RSS MB | PSS MB | PSS anon | PSS file |",
            "|---|---|--:|--:|--:|--:|--:|"]
    for scenario, runs in results.items():
        roles = sorted({name for run in runs for name in run})
        total = []
        for name in roles:
            present = [run[name] for run in runs if name in run]
            n = int(statistics.median(p[0] for p in present))
            cols = [statistics.median(p[i] for p in present) for i in range(1, 5)]
            rows.append(f"| {scenario} | {name} | {n} | " + " | ".join(f"{c:.1f}" for c in cols) + " |")
        for run in runs:
            total.append(sum(v[0] * v[2] for v in run.values()))
        rows.append(f"| {scenario} | **total PSS** | | | {statistics.median(total):.1f} | | |")
    return "\n".join(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--eukhe", default=os.path.join(ROOT, "target", "release", "eukhe"))
    parser.add_argument("--kernel-python", default=os.environ.get("EUKHE_KERNEL_PYTHON"))
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--scenarios", default=",".join(SCENARIOS))
    parser.add_argument("--fixture")
    parser.add_argument("--json")
    args = parser.parse_args()
    if not sys.platform.startswith("linux"):
        sys.exit("ram_map.py reads /proc/<pid>/smaps_rollup: Linux only")
    if not args.kernel_python:
        sys.exit("no kernel interpreter: pass --kernel-python or set EUKHE_KERNEL_PYTHON")
    args.eukhe = os.path.abspath(args.eukhe)
    names = args.scenarios.split(",")
    unknown = [n for n in names if n not in SCENARIOS]
    if unknown:
        sys.exit(f"unknown scenarios {unknown}; known: {', '.join(SCENARIOS)}")
    root = tempfile.mkdtemp(prefix="ram-map.")
    if args.fixture is None:
        args.fixture = os.path.join(root, "fixture")
    args.fixture = os.path.abspath(args.fixture)
    results = {}
    try:
        for run in range(args.runs):
            for name in names:
                path = args.fixture if name == "tui-2000" else os.path.join(root, f"{name}-{run}")
                if name == "tui-2000":
                    build_fixture(args)
                home = Home(path, args.eukhe, args.kernel_python)
                try:
                    if name != "print":
                        home.start()
                    snap = SCENARIOS[name](home, args)
                finally:
                    home.stop()
                    if name != "tui-2000":
                        shutil.rmtree(path, ignore_errors=True)
                results.setdefault(name, []).append(summarize(snap))
                print(f"run {run + 1}/{args.runs} {name}: "
                      f"{sum(v[0] * v[2] for v in results[name][-1].values()):.1f} MB PSS",
                      file=sys.stderr)
    finally:
        shutil.rmtree(root, ignore_errors=True)
    print(table(results))
    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
