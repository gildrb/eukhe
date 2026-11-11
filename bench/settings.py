"""Bench paths and binaries: each from its flag, else its EUKHE_BENCH_* variable, else the default."""
import os
import pathlib
import shutil

BENCH = pathlib.Path(__file__).resolve().parent
REPO = BENCH.parent

# name: (env variable, default, help). A default may name {dir}: the resolved data dir.
SETTINGS = {
    "dir": ("EUKHE_BENCH_DIR", "/var/tmp/eukhe-bench-data",
            "data dir: fixtures, results, work dirs, logs, venvs (keep it outside any repo: agents read "
            "AGENTS.md files of parent dirs)"),
    "eukhe": ("EUKHE_BENCH_EUKHE", str(REPO / "target/release/eukhe"),
              "eukhe binary (inside its source checkout or a packaged layout, so it finds its skills and runtime)"),
    "omp": ("EUKHE_BENCH_OMP", "omp", "omp binary"),
    "kernel_dir": ("EUKHE_BENCH_KERNEL_DIR", "{dir}/kernel",
                   "eukhe kernel directory shared by every run (its pinned Python, fetched with `eukhe kernel install` when missing)"),
    "venv": ("EUKHE_BENCH_VENV", "{dir}/venv",
             "Python venv with Playwright: python3 of the agents' PATH and of the graders (made with uv when missing)"),
    "auth": ("EUKHE_BENCH_AUTH", "~/.eukhe/auth.json",
             "eukhe auth.json to copy from (read only; each run gets a copy without refresh tokens)"),
    "models": ("EUKHE_BENCH_MODELS", "~/.eukhe/models.json", "eukhe models.json to copy from (optional)"),
    "chromium": ("EUKHE_BENCH_CHROMIUM", "chromium", "Chromium for the browser graders"),
    "model": ("EUKHE_BENCH_MODEL", "", "run every task with this model key instead of the task's own"),
}


def add_flags(parser, names=tuple(SETTINGS)):
    for name in names:
        env, default, text = SETTINGS[name]
        parser.add_argument(f"--{name.replace('_', '-')}", dest=name, help=f"{text} [${env}, default {default!r}]")


def apply(args):
    """Flags win over the environment; exported so child processes (batch -> run -> grade) see them."""
    for name, (env, _, _) in SETTINGS.items():
        value = getattr(args, name, None)
        if value:
            os.environ[env] = value


def get(name):
    env, default, _ = SETTINGS[name]
    value = os.environ.get(env) or default
    if "{dir}" in value:
        value = value.format(dir=get("dir"))
    return value


def path(name):
    return pathlib.Path(get(name)).expanduser()


def binary(name):
    """An executable setting resolved through PATH when it is a bare name."""
    value = get(name)
    found = shutil.which(value) if "/" not in value else str(pathlib.Path(value).expanduser().resolve())
    if not found or not os.access(found, os.X_OK):
        raise SystemExit(f"bench: {name} binary not found: {value} (set --{name} or ${SETTINGS[name][0]})")
    return pathlib.Path(found)
