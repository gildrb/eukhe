#!/usr/bin/env python3
"""The nightly gate and release of eukhe. A systemd user timer runs it once
a night.

  ci_nightly.py run     the full gate (`make ci-local`) on origin/main, in
                        the gate worktree (<repo>-ci beside the main
                        checkout: a path under .git hides the tests from
                        vitest and makes test socket paths too long). When
                        it passes, it starts the release of that commit
                        (`gh workflow run eukhe-release.yml -f sha=<commit>`).
                        When it fails, nothing is released.
  ci_nightly.py status  the result of the last run.

Each run appends its result to ~/.eukhe/ci/nightly.log: one line with the
time, the commit and the result, and for a failure the failed gates and test
units. The full output of the last run is ~/.eukhe/ci/nightly-last.log. A
commit that already has an eukhe-v* tag is not run again. The
nix/release.json commit a release adds on main is never released itself
(eukhe-release.yml refuses it): the commit under it is the one run. One run
at a time (flock on <git common dir>/eukhe-ci-nightly.lock).
"""

from __future__ import annotations

import fcntl
import locale
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# The checkout this script is in, as invoked (symlinks kept, as `cd` keeps
# them): the gate worktree's path is the same every night.
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
USAGE = "usage: .github/scripts/ci_nightly.py run|status"
STATE = Path.home() / ".eukhe" / "ci"
SUMMARY = STATE / "nightly.log"
LAST = STATE / "nightly-last.log"
RECORD = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T")
FAILED = re.compile(r"gate '.*' FAILED|^ +(TRY 2 )?FAIL \[|^test .* FAILED$|^  flaky: ")
FLAKY = re.compile(r"^  flaky: ")


def git(*args: str) -> str:
    """git's stdout without its trailing newlines; raises when git fails."""
    return subprocess.run(["git", *args], stdout=subprocess.PIPE, text=True, check=True).stdout.rstrip("\n")


def tee(lines: list[str]) -> None:
    """Print the lines and append them to the summary."""
    text = "".join(f"{line}\n" for line in lines)
    sys.stdout.write(text)
    with SUMMARY.open("a", encoding="utf-8") as summary:
        summary.write(text)


def matching(pattern: re.Pattern[str]) -> list[str]:
    """The lines of the last run's output that match, as `grep -E`."""
    with LAST.open(encoding="utf-8", errors="replace") as log:
        return [line.rstrip("\n") for line in log if pattern.search(line.rstrip("\n"))]


def sorted_unique(lines: list[str]) -> list[str]:
    """`sort -u` in the locale's collation."""
    locale.setlocale(locale.LC_COLLATE, "")
    return sorted(set(lines), key=locale.strxfrm)


def status() -> int:
    if not SUMMARY.is_file() or SUMMARY.stat().st_size == 0:
        print(f"no nightly run yet ({SUMMARY} is empty)")
        return 0
    # The last record: its result line and the detail lines under it.
    lines = SUMMARY.read_text(encoding="utf-8", errors="replace").split("\n")
    if lines[-1] == "":
        lines.pop()
    record: list[str] = []
    for line in lines:
        if RECORD.match(line):
            record = []
        record.append(line)
    sys.stdout.write("".join(f"{line}\n" for line in record))
    return 0


def run() -> int:
    if shutil.which("gh") is None:
        print("gh not installed: the release cannot start", file=sys.stderr)
        return 1
    STATE.mkdir(parents=True, exist_ok=True)
    common = os.path.normpath(os.path.join(ROOT, git("rev-parse", "--git-common-dir")))
    worktree = f"{os.path.dirname(common)}-ci"
    # Not inherited by the gate (Python's descriptors are not): a process
    # the gate leaves behind never holds the lock.
    lock = os.open(f"{common}/eukhe-ci-nightly.lock", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o666)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("another nightly run is in progress", file=sys.stderr)
        return 1
    git("fetch", "--quiet", "--tags", "origin")
    sha = git("rev-parse", "origin/main")
    if git("log", "-1", "--format=%s", sha).startswith("nix: release.json for "):
        sha = git("rev-parse", f"{sha}^")
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    released = git("tag", "--points-at", sha, "--list", "eukhe-v*")
    if released:
        tee([f"{stamp} {sha[:12]} skipped: already released as {released.replace(chr(10), ', ')}"])
        return 0
    previous = subprocess.run(
        ["git", "describe", "--tags", "--abbrev=0", "--match", "eukhe-v*", sha],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
    ).stdout.rstrip("\n")
    if os.path.exists(f"{worktree}/.git"):
        git("-C", worktree, "checkout", "--quiet", "--detach", "--force", sha)
        git("-C", worktree, "clean", "--quiet", "-fdx", "-e", "/target/", "-e", "node_modules/")
    else:
        git("worktree", "prune")
        git("worktree", "add", "--quiet", "--detach", "--force", worktree, sha)
    # Every night builds from an empty build dir: cargo never deletes stale
    # build files, and one day of gate runs grew this dir to 410 GB.
    subprocess.run(["cargo", "clean", "--quiet"], cwd=worktree, stdin=subprocess.DEVNULL, check=True)
    start = time.monotonic()
    env = dict(os.environ, CI_LOCAL_SECRETS_RANGE=f"{previous}..{sha}" if previous else sha)
    with LAST.open("w") as last:
        code = subprocess.run(
            ["nice", "-n", "10", "make", "--no-print-directory", "-C", worktree, "ci-local"],
            stdin=subprocess.DEVNULL,
            stdout=last,
            stderr=subprocess.STDOUT,
            env=env,
        ).returncode
    minutes = int(time.monotonic() - start) // 60
    if code:
        failed = [re.sub(r"^ *", "  ", line, count=1) for line in matching(FAILED)]
        tee([f"{stamp} {sha[:12]} FAILED after {minutes} min: no release (full output: {LAST})", *sorted_unique(failed)])
        return 1
    # The release runs on GitHub (remote `github`); `origin` is the Forgejo
    # workspace. gh prefers an `upstream` remote over the others, so name the
    # GitHub repo explicitly.
    repo = re.sub(r"\.git$", "", re.sub(r".*github\.com[:/]", "", git("remote", "get-url", "github")))
    subprocess.run(["gh", "workflow", "run", "eukhe-release.yml", "--repo", repo, "--ref", "main", "-f", f"sha={sha}"], check=True)
    tee([f"{stamp} {sha[:12]} passed in {minutes} min: release started", *sorted_unique(matching(FLAKY))])
    return 0


def main() -> int:
    if len(sys.argv) < 2 or not sys.argv[1]:
        print(USAGE, file=sys.stderr)
        return 1
    os.chdir(ROOT)
    modes = {"run": run, "status": status}
    if sys.argv[1] not in modes:
        print(USAGE, file=sys.stderr)
        return 2
    sys.stdout.reconfigure(line_buffering=True)
    try:
        return modes[sys.argv[1]]()
    except subprocess.CalledProcessError as failed:
        return failed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
