#!/usr/bin/env python3
"""One run: run.py [flags] <eukhe|omp> <task> <run-no>.

Fresh repo(s) and an isolated HOME per run, same model and thinking for both tools (the task's, or --model).
Results in <dir>/results/<label>/<task>/<run>/ (summary.json, every turn's JSON stream and stderr), the run's
repo and HOME in <dir>/work/<label>/<task>/<run>/. <label> is the tool, then -<model> with --model, then
-<tag> with --tag.
"""
import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import time

import settings
import tasks

SMALL = "claude-haiku-5-5"
TURN_TIMEOUT = 40 * 60
MODELS = {
    "opus": ("anthropic", "claude-opus-5-5", "medium"),
    "glm": ("zai", "glm-5.3-flash", "high"),
    "haiku": ("anthropic", "claude-haiku-5-5", "low"),
}
# How omp takes each provider's credential: (env variable, auth.json field).
OMP_AUTH_ENV = {"anthropic": ("ANTHROPIC_OAUTH_TOKEN", "access"), "zai": ("ZAI_API_KEY", "key")}
VENV_PYTHON = "3.14"
VENV_PACKAGES = ("playwright==1.64.1", "pillow==13.0.0")
GENERATORS = ("gen_small", "gen_fanout", "gen_relay", "gen_tickets", "gen_sheet", "gen_migrate")


def data():
    return settings.path("dir")


def venv_python():
    return settings.path("venv") / "bin/python3"


def base_env(home):
    rt = home / "run"
    rt.mkdir(parents=True, exist_ok=True, mode=0o700)
    return {
        # The bench venv (python3 with Playwright) first, as the browser fixtures' AGENTS.md promises.
        "PATH": f"{venv_python().parent}:{os.environ['PATH']}",
        "HOME": str(home),
        "USER": os.environ.get("USER", ""),
        "LANG": "C.UTF-8",
        "TERM": "dumb",
        "XDG_RUNTIME_DIR": str(rt),
        # As in a NixOS login session: /etc/bashrc rebuilds PATH from the profile (dropping the launch PATH)
        # in any bash that does not see these markers. Harmless elsewhere.
        "SHELL": os.environ.get("SHELL", "/bin/bash"),
        "__NIXOS_SET_ENVIRONMENT_DONE": "1",
        "__ETC_PROFILE_DONE": "1",
        "XDG_CONFIG_HOME": str(home / ".config"),
        "XDG_CACHE_HOME": str(home / ".cache"),
        "XDG_DATA_HOME": str(home / ".local/share"),
        "XDG_STATE_HOME": str(home / ".local/state"),
        "NO_COLOR": "1",
    }


def provider_auth(provider):
    """The provider's auth.json entry, refresh token blanked: a run can never rotate the user's login."""
    src = settings.path("auth")
    entry = json.loads(src.read_text()).get(provider) if src.is_file() else None
    if not isinstance(entry, dict):
        raise SystemExit(f"bench: no {provider} login in {src}")
    expires = entry.get("expires")
    if isinstance(expires, int) and expires < time.time() * 1000:
        raise SystemExit(f"bench: the {provider} access token in {src} has expired; run eukhe once to refresh it")
    return {**entry, "refresh": ""} if "refresh" in entry else dict(entry)


def kill_home(home):
    """Kill every process running with this HOME (daemons, workers, kernels, servers)."""
    needle = f"HOME={home}".encode() + b"\0"
    for p in pathlib.Path("/proc").iterdir():
        if not p.name.isdigit() or int(p.name) == os.getpid():
            continue
        try:
            if needle in (p / "environ").read_bytes():
                os.kill(int(p.name), signal.SIGKILL)
        except OSError:
            pass


def private_tmp(cmd, tmp):
    """cmd with `tmp` bound over /tmp: runs in parallel (and earlier runs) never share scratch files such as
    /tmp/shot.png, which a model then reads, attaches or is refused to overwrite as if they were its own."""
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise SystemExit("bench: bwrap is needed to give each run its own /tmp")
    return [bwrap, "--dev-bind", "/", "/", "--bind", str(tmp), "/tmp", "--", *cmd]


# ---------------------------------------------------------------- one-time setup

@contextlib.contextmanager
def setup_lock():
    data().mkdir(parents=True, exist_ok=True)
    with open(data() / ".setup.lock", "w") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        yield


def ensure_venv():
    venv = settings.path("venv")
    stamp = venv / ".bench-ready"
    if stamp.exists() or (venv_python().exists() and "EUKHE_BENCH_VENV" in os.environ):
        return
    uv = shutil.which("uv")
    if not uv:
        raise SystemExit(f"bench: uv is needed to make the bench venv {venv} (or pass --venv)")
    subprocess.run([uv, "venv", "-q", "--allow-existing", "--python", VENV_PYTHON, str(venv)], check=True)
    subprocess.run([uv, "pip", "install", "-q", "--python", str(venv_python()), *VENV_PACKAGES], check=True)
    stamp.touch()


def ensure_kernel_venv(eukhe):
    """A kernel venv every eukhe run shares: a fresh HOME has none, and a session never downloads one."""
    kv = settings.path("kernel_venv")
    stamp = kv / ".bench-ready"
    if stamp.exists() or ((kv / "bin/python").exists() and "EUKHE_BENCH_KERNEL_VENV" in os.environ):
        return
    if "EUKHE_BENCH_KERNEL_VENV" in os.environ:
        raise SystemExit(f"bench: no kernel venv at {kv}")
    home = data() / "kernel-home"
    env = {**base_env(home), "PATH": f"{eukhe.parent}:{os.environ['PATH']}", "EUKHE_KERNEL_VENV": str(kv),
           "EUKHE_CODING_AGENT_DIR": str(home / ".eukhe"), "EUKHE_DAEMON_SOCKET": str(home / "run/daemon.sock")}
    try:
        rc = subprocess.run([str(eukhe), "kernel", "install"], env=env).returncode
    finally:
        kill_home(home)
    if rc:
        raise SystemExit(f"bench: `eukhe kernel install` failed ({rc})")
    stamp.touch()


def ensure_fixtures():
    """Generate fixtures, expected answers, reference solutions and hidden tests when bench/gen changed."""
    gen = settings.BENCH / "gen"
    digest = hashlib.sha256()
    for p in sorted(gen.rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts:
            digest.update(str(p.relative_to(gen)).encode() + b"\0" + p.read_bytes())
    stamp = data() / "fixtures" / ".bench-ready"
    if stamp.is_file() and stamp.read_text() == digest.hexdigest():
        return
    for sub in ("fixtures", "expected", "ref", "hidden"):
        shutil.rmtree(data() / sub, ignore_errors=True)
    for g in GENERATORS:
        subprocess.run([str(venv_python()), "-B", str(gen / f"{g}.py"), str(data())], check=True,
                       stdout=subprocess.DEVNULL)
    for src in sorted((gen / "static").iterdir()):
        shutil.copytree(src, data() / "fixtures" / src.name)
    stamp.write_text(digest.hexdigest())


def prepare(tools):
    with setup_lock():
        ensure_venv()
        ensure_fixtures()
        if "eukhe" in tools:
            ensure_kernel_venv(settings.binary("eukhe"))


# ---------------------------------------------------------------- one run

def eukhe_setup(home, model, spec):
    provider = MODELS[model][0]
    agent = home / ".eukhe"
    agent.mkdir(parents=True, exist_ok=True)
    auth = {p: provider_auth(p) for p in {"anthropic", provider}}
    (agent / "auth.json").touch(mode=0o600)
    (agent / "auth.json").write_text(json.dumps(auth))
    src = settings.path("models")
    models = json.loads(src.read_text()) if src.is_file() else {"providers": {}}
    if spec.get("ctx"):
        models["providers"].setdefault(provider, {}).setdefault("modelOverrides", {})[MODELS[model][1]] = {
            "contextWindow": spec["ctx"]}
    (agent / "models.json").write_text(json.dumps(models))
    # The helper models on Anthropic, so a run needs no local model.
    (agent / "config.cfg").write_text(
        f"set memory.model anthropic/{SMALL}\n"
        "set memory.thinking low\n"
        f"set auxiliaryModel anthropic/{SMALL}\n"
        f"set modelRoles.tiny anthropic/{SMALL}\n"
        f"set gateway.signal.model anthropic/{SMALL}\n" + spec.get("eukhe_cfg", "")
    )
    env = base_env(home)
    env["PATH"] = f"{settings.binary('eukhe').parent}:{env['PATH']}"
    env["EUKHE_CODING_AGENT_DIR"] = str(agent)
    env["EUKHE_DAEMON_SOCKET"] = str(home / "run/daemon.sock")
    env["EUKHE_KERNEL_VENV"] = str(settings.path("kernel_venv"))
    return env


def omp_setup(home, model, spec):
    provider, name, _ = MODELS[model]
    agent = home / ".omp/agent"
    agent.mkdir(parents=True, exist_ok=True)
    if spec.get("ctx"):
        (agent / "models.yml").write_text(
            f"providers:\n  {provider}:\n    modelOverrides:\n      {name}:\n        contextWindow: {spec['ctx']}\n")
    env = base_env(home)
    env["PI_CODING_AGENT_DIR"] = str(agent)
    var, field = OMP_AUTH_ENV[provider]
    env[var] = provider_auth(provider)[field]
    return env


def command(tool, model, turn, repo, prompt):
    provider, name, thinking = MODELS[model]
    cont = ["-c"] if turn > 1 else []
    if tool == "eukhe":
        return [str(settings.binary("eukhe")), "-p", "--mode", "json", "--cwd", str(repo), "--provider", provider,
                "--model", name, "--thinking", thinking] + cont + ["--", prompt]
    return [str(settings.binary("omp")), "-p", "--mode", "json", "--cwd", str(repo), "--model", f"{provider}/{name}",
            "--thinking", thinking, "--auto-approve", "--no-title"] + cont + [prompt]


def messages(jsonl):
    out = []
    for line in jsonl.read_text(errors="replace").splitlines():
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") == "message_end" and isinstance(d.get("message"), dict):
            out.append(d["message"])
    return out


def content_list(m):
    c = m.get("content")
    return c if isinstance(c, list) else [{"type": "text", "text": str(c)}]


def stream_stats(jsonl, prompt):
    """The turn's cost and calls from its JSON stream. injected_notes: non-prompt user/custom messages."""
    cost, calls, llm, errors, tool_errors, notes = 0.0, 0, 0, [], 0, []
    final, seen_prompt = "", False
    for m in messages(jsonl):
        role = m.get("role")
        content = content_list(m)
        if role == "assistant":
            llm += 1
            cost += float(((m.get("usage") or {}).get("cost") or {}).get("total") or 0)
            calls += sum(1 for c in content if c.get("type") == "toolCall")
            text = "".join(c.get("text", "") for c in content if c.get("type") == "text").strip()
            if text:
                final = text
            if m.get("stopReason") in ("error", "aborted"):
                errors.append(str(m.get("errorMessage", m.get("stopReason")))[:300])
        elif role == "toolResult":
            tool_errors += bool(m.get("isError"))
        else:
            text = " ".join(c.get("text", "") for c in content if isinstance(c, dict))
            if role == "user" and not seen_prompt and text.strip() == prompt.strip():
                seen_prompt = True
                continue
            notes.append(f"{role}/{m.get('customType')}: {text[:160]}")
    return {"cost": round(cost, 4), "tool_calls": calls, "llm_calls": llm, "tool_errors": tool_errors,
            "errors": errors, "injected_notes": notes, "final": final}


def tool_call_texts(jsonl):
    """Every tool call's arguments as text (for informational greps)."""
    return [f"{c.get('name')}: {json.dumps(c.get('arguments'))}" for m in messages(jsonl)
            if m.get("role") == "assistant" for c in content_list(m) if c.get("type") == "toolCall"]


def label_of(tool, model, tag):
    return "-".join(x for x in (tool, model, tag) if x)


class Run:
    def __init__(self, tool, task, run, model=None, tag=None):
        self.tool, self.task, self.run = tool, task, run
        self.spec = tasks.TASKS[task]
        self.model = model or self.spec["model"]
        self.label = label_of(tool, model, tag)
        self.out = data() / "results" / self.label / task / run
        self.work = data() / "work" / self.label / task / run
        for d in (self.out, self.work):
            if d.exists():
                shutil.rmtree(d)
        self.out.mkdir(parents=True)
        self.home = self.work / "home"
        self.tmp = self.work / "tmp"
        self.tmp.mkdir(parents=True)
        setup = eukhe_setup if tool == "eukhe" else omp_setup
        self.env = setup(self.home, self.model, self.spec)
        self.turns = []

    def make_repo(self, fixture, name="repo"):
        repo = self.work / name
        shutil.copytree(data() / "fixtures" / fixture, repo, ignore=shutil.ignore_patterns(".bench-ready"))
        git = ["git", "-C", str(repo), "-c", "user.name=bench", "-c", "user.email=bench@example.invalid",
               "-c", "commit.gpgsign=false"]
        for args in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "fixture"]):
            subprocess.run(git + args, check=True)
        return repo

    def turn(self, repo, n, prompt, label, kill_after=None):
        """Run one turn to its end (or kill everything of this HOME after kill_after seconds)."""
        cmd = private_tmp(command(self.tool, self.model, n, repo, prompt), self.tmp)
        so_path = self.out / f"{label}.stdout.jsonl"
        t0 = time.time()
        with open(so_path, "w") as so, open(self.out / f"{label}.stderr.log", "w") as se:
            proc = subprocess.Popen(cmd, cwd=repo, env=self.env, stdout=so, stderr=se)
            try:
                rc = proc.wait(timeout=kill_after or TURN_TIMEOUT)
            except subprocess.TimeoutExpired:
                rc = "killed" if kill_after else "timeout"
                kill_home(self.home)
                proc.wait()
        rec = {"label": label, "exit": rc, "wall_s": round(time.time() - t0, 1), **stream_stats(so_path, prompt)}
        self.turns.append(rec)
        print(json.dumps({k: rec[k] for k in ("label", "exit", "wall_s", "cost", "tool_calls")}), flush=True)
        return rec

    def rev(self):
        """The binary's version, plus its source commit when it sits in a git checkout (or names one in REV)."""
        binary = settings.binary(self.tool)
        version = subprocess.run([str(binary), "--version"], capture_output=True, text=True, env=self.env,
                                 cwd=self.work).stdout.strip()
        rev_file = binary.parent / "REV"
        commit = rev_file.read_text().strip() if rev_file.is_file() else subprocess.run(
            ["git", "-C", str(binary.parent), "describe", "--always", "--dirty", "--abbrev=12"],
            capture_output=True, text=True).stdout.strip()
        return f"{version} {commit}".strip()

    def finish(self, grade):
        summary = {"tool": self.tool, "label": self.label, "task": self.task, "run": self.run,
                   "model": MODELS[self.model], "rev": self.rev(), "turns": self.turns, **grade,
                   "storage": tasks.storage_usage(self.tool, self.home)}
        summary["passed"] = all(grade["checks"].values())
        (self.out / "summary.json").write_text(json.dumps(summary, indent=2))
        print(json.dumps({"passed": summary["passed"], "failed": [k for k, v in grade["checks"].items() if not v]}))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tool", choices=("eukhe", "omp"))
    ap.add_argument("task", choices=sorted(tasks.TASKS))
    ap.add_argument("run")
    ap.add_argument("--tag", help="label suffix, e.g. `before` and `after` for two eukhe builds")
    settings.add_flags(ap)
    args = ap.parse_args()
    settings.apply(args)
    model = settings.get("model") or None
    if model and model not in MODELS:
        raise SystemExit(f"bench: unknown model {model} (one of {', '.join(MODELS)})")
    prepare({args.tool})
    r = Run(args.tool, args.task, args.run, model, args.tag)
    grade = {"checks": {"graded": False}, "info": {}}
    try:
        grade = r.spec["flow"](r)
    except Exception:  # the run's record must survive a harness error
        import traceback
        grade = {"checks": {"harness_ok": False}, "info": {"error": traceback.format_exc()[-1500:]}}
        print(grade["info"]["error"], file=sys.stderr)
    finally:
        kill_home(r.home)
        for p in (r.home / ".eukhe/auth.json", r.home / ".eukhe/models.json"):
            p.unlink(missing_ok=True)
        r.finish(grade)


if __name__ == "__main__":
    main()
