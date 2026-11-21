#!/usr/bin/env python3
"""startup_bench.py BIN [BIN ...]: how long `eukhe` takes to start, per binary.

The median wall time and CPU time (user + sys) of N runs (env N, default 10),
the binaries interleaved so a busy machine weighs on each alike. Each run has
a fresh HOME; `SCEN=a,b` keeps only those scenarios:

- version, help: `--version`, `--help`.
- slash-fresh: a one-shot `-p "/autonomous status"` (json mode, a fake key)
  on a home without the pinned Python kernel: the first start on a machine.
- slash-kernel: the same with `~/.eukhe/kernel` linked in (an installed kernel).
- prompt-stub: a one-shot `-p` whose model is a local OpenAI-compatible stub
  that answers "ok" at once (kernel linked in).

A release build compares with an older release: within 10 % is the budget.
"""
import json
import os
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


def chunk(choices, usage=None):
    body = {"id": "c1", "object": "chat.completion.chunk", "created": 0, "model": "mock-1",
            "choices": choices}
    if usage:
        body["usage"] = usage
    return "data: " + json.dumps(body) + "\n\n"


class Stub(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def do_POST(self):
        self.rfile.read(int(self.headers.get("content-length", "0")))
        body = (chunk([{"index": 0, "delta": {"role": "assistant", "content": "ok"},
                        "finish_reason": None}])
                + chunk([{"index": 0, "delta": {}, "finish_reason": "stop"}])
                + chunk([], {"prompt_tokens": 10, "completion_tokens": 1, "total_tokens": 11})
                + "data: [DONE]\n\n").encode()
        self.send_response(200)
        self.send_header("content-type", "text/event-stream")
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    n = int(os.environ.get("N", "10"))
    only = os.environ.get("SCEN")
    bins = [os.path.abspath(b) for b in sys.argv[1:]]
    if not bins:
        sys.exit(__doc__)
    server = ThreadingHTTPServer(("127.0.0.1", 0), Stub)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    models = json.dumps({"providers": {"stub": {
        "api": "openai-completions",
        "baseUrl": f"http://127.0.0.1:{server.server_address[1]}/v1",
        "apiKey": "sk-stub",
        "models": [{"id": "mock-1", "name": "Mock 1", "api": "openai-completions",
                    "contextWindow": 128000, "maxTokens": 4096}],
    }}})
    kernel = os.path.expanduser("~/.eukhe/kernel")
    slash = ["--provider", "anthropic", "--model", "claude-haiku-5-5", "--api-key", "sk-ant-fake",
             "--mode", "json", "-p", "/autonomous status"]
    stub = ["--provider", "stub", "--model", "mock-1", "--mode", "json", "-p", "say ok"]
    scenarios = {
        "version": (["--version"], False, False),
        "help": (["--help"], False, False),
        "slash-fresh": (slash, False, False),
        "slash-kernel": (slash, True, False),
        "prompt-stub": (stub, True, True),
    }
    if not os.path.isdir(kernel):
        print(f"no {kernel}: slash-kernel and prompt-stub run without a kernel", file=sys.stderr)
    root = tempfile.mkdtemp(prefix="startup-bench.", dir=os.environ.get("BENCH_DIR"))
    results = {}
    try:
        for _ in range(n):
            for name, (args, with_kernel, with_stub) in scenarios.items():
                if only and name not in only.split(","):
                    continue
                for binary in bins:
                    home = tempfile.mkdtemp(dir=root)
                    os.makedirs(os.path.join(home, "run"))
                    os.makedirs(os.path.join(home, ".eukhe"))
                    if with_kernel and os.path.isdir(kernel):
                        os.symlink(kernel, os.path.join(home, ".eukhe", "kernel"))
                    if with_stub:
                        with open(os.path.join(home, ".eukhe", "models.json"), "w") as f:
                            f.write(models)
                    env = dict(os.environ, HOME=home, XDG_RUNTIME_DIR=os.path.join(home, "run"))
                    before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    start = time.monotonic()
                    code = subprocess.run([binary, *args], env=env, cwd=home,
                                          stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                          stderr=subprocess.DEVNULL).returncode
                    wall = time.monotonic() - start
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
                    results.setdefault((name, binary), []).append((wall, cpu, code))
                    shutil.rmtree(home, ignore_errors=True)
    finally:
        shutil.rmtree(root, ignore_errors=True)
        server.shutdown()
    width = max(len(b) for b in bins)
    print(f"{'scenario':13} {'binary':{width}} {'wall ms':>8} {'cpu ms':>8} exit")
    for (name, binary), runs in results.items():
        wall = statistics.median(r[0] for r in runs) * 1000
        cpu = statistics.median(r[1] for r in runs) * 1000
        codes = ",".join(str(c) for c in sorted({r[2] for r in runs}))
        print(f"{name:13} {binary:{width}} {wall:8.0f} {cpu:8.0f} {codes}")


if __name__ == "__main__":
    main()
