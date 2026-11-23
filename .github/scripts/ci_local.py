#!/usr/bin/env python3
"""The CI gates of eukhe. They run only here: GitHub runs no gate. prek
runs fast and pre-push as git hooks (.pre-commit-config.yaml; `make hooks`
installs them); the nightly run (.github/scripts/ci_nightly.py) runs full
and releases only when it passes.

  ci_local.py fast      `make ci-fast`, the pre-commit gate (< 1 min):
                        rustfmt, the crate layering
                        (.github/scripts/check_crate_layers.py), the secrets
                        scan of the staged diff, the embedded JavaScript
                        against its TypeScript sources (when the staged
                        change touches a .ts or .js file under crates/), and
                        clippy on the crates the staged change touches.
  ci_local.py pre-push  the pre-push gate (< 5 min), on the pushed commits
                        (PRE_COMMIT_FROM_REF..PRE_COMMIT_TO_REF, from prek),
                        in this worktree: rustfmt, their secrets scan, clippy
                        and the unit tests (nextest profile pre-push: no e2e
                        suite) of the crates they touch, the proofs their
                        Bend change can reach (.github/scripts/bend_proofs.py),
                        the embedded JavaScript (as in fast), the dashboard
                        UI (as in full, when they touch
                        crates/eukhe-dashboard/ui/), and the laws against
                        LAWS.lock. No lock: every worktree pushes at any time.
  ci_local.py full      `make ci-local`, the nightly gate (< 30 min):
                        everything, on the current tree: every test (nextest
                        profile nightly, and the doctests), `bend PROOF.bend
                        --verdict`, the TypeScript SDK (`make sdk-ts`).
  ci_local.py lock      `make lock`: re-lock the laws in seconds. The proofs
                        the change since origin/main can reach, then
                        LAWS.lock written.

Each gate prints its name; a failed gate prints `ci-<mode>: gate <name>
FAILED` and the script stops with its exit code. The full gate runs the Rust
lane (clippy, tests, the TypeScript SDK) and the other lane (secrets, deny,
laws, the embedded JavaScript, runtime tests, dashboard UI) at the same time;
the second lane's log prints when it ends.

A failed test runs once more (.config/nextest.toml, retries = 1): a pass then
is flaky, named as `  flaky: <test>`, and does not fail the gate (the nightly
summary keeps the names, so the timing bug gets fixed); a second failure
fails it.

The tools and the build environment (cargo-nextest, sccache) come from
mise.toml: the script trusts, installs and loads it.

CI_LOCAL_SECRETS_RANGE: the `git log` range that full and pre-push scan for
secrets. Default: origin/main..HEAD.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from fnmatch import fnmatchcase
from pathlib import Path

import ci_pr_crates
import pinned_bend
import pinned_skill
from toolchain import pins

ROOT = Path(__file__).resolve().parents[2]
USAGE = "usage: .github/scripts/ci_local.py fast|pre-push|full|lock"
MODE = ""

# A change: (path, old path) rows, the old path of a rename or copy, empty
# for the others (the rows of ci_pr_crates.py).
Rows = list[tuple[str, str]]


class Failed(Exception):
    """A step failed with this exit code (bash's `set -e` in a gate)."""

    def __init__(self, code: int) -> None:
        super().__init__(code)
        self.code = code


def exit_code(returncode: int) -> int:
    """A process's exit code as a shell reports it (128 + a signal)."""
    return 128 - returncode if returncode < 0 else returncode


def run(*args: str, env: dict[str, str] | None = None) -> None:
    code = exit_code(subprocess.run(args, env=env).returncode)
    if code:
        raise Failed(code)


def output(*args: str) -> str:
    """The command's stdout without its trailing newlines; Failed when it fails."""
    result = subprocess.run(args, stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise Failed(exit_code(result.returncode))
    return result.stdout.rstrip("\n")


def make(target: str) -> None:
    run("make", "--no-print-directory", target)


def gate(name: str, step, *args) -> None:
    print(f"==> ci-{MODE}: {name}")
    try:
        step(*args)
    except FileNotFoundError as missing:
        # A command that is not installed: the shell's 127.
        print(f"{missing.filename}: command not found", file=sys.stderr)
        code = 127
    except Failed as failed:
        code = failed.code
    else:
        return
    print(f"ci-{MODE}: gate '{name}' FAILED (exit {code})", file=sys.stderr)
    raise SystemExit(code)


def check_bend() -> None:
    if pinned_bend.find() is None:
        print(pinned_bend.missing(), file=sys.stderr)
        raise Failed(1)


def check_lean() -> None:
    version = pins()["LEAN_VERSION"]
    if shutil.which("lean") is None:
        print(f"lean is not installed. bend --verdict needs Lean {version}, the release that .github/scripts/toolchain.env pins.")
        raise Failed(1)
    found = re.search(r"^Lean \(version ([0-9.]*),", output("lean", "--version"), re.MULTILINE)
    have = found.group(1) if found else ""
    if have != version:
        print(f"lean {have} is installed, but .github/scripts/toolchain.env pins Lean {version}. Install Lean {version}.")
        raise Failed(1)


def check_tools(*tools: str) -> None:
    missing = [tool for tool in tools if shutil.which(tool) is None]
    if missing:
        print(f"not installed: {' '.join(missing)} (mise.toml and nix develop have them)")
        raise Failed(1)


def change_rows(*args: str) -> Rows:
    """A change as ci_pr_crates.py rows, from `git diff --name-status` with
    the arguments given (--cached, or two commits)."""
    rows = []
    for line in output("git", "diff", "--name-status", "-M", "--no-color", *args).splitlines():
        fields = line.split("\t")
        if fields[0][:1] in ("R", "C"):
            rows.append((fields[2], fields[1]))
        else:
            rows.append((fields[1], ""))
    return rows


def touched(rows: Rows, patterns: tuple[str, ...], skip: tuple[str, ...] = ()) -> bool:
    """Whether a path of the change (either side of a rename) matches one of
    `patterns` (shell globs: `*` matches `/` too) and none of `skip`."""
    return any(
        not any(fnmatchcase(path, pattern) for pattern in skip)
        and any(fnmatchcase(path, pattern) for pattern in patterns)
        for row in rows
        for path in row
    )


def docs_only(paths: list[str]) -> bool:
    """A docs-only change (the hooks skip rule): every path is a Markdown
    file at the repository root. Crates embed their own Markdown, so
    Markdown elsewhere counts as code."""
    paths = [path for path in paths if path]
    return bool(paths) and all(path.endswith(".md") and "/" not in path for path in paths)


# The paths no crate builds or tests from: the gate tooling, the GitHub and
# Nix files, the agent rules, the docs (spec/), the laws and proofs (the
# proofs and laws lock gates check them, spec/'s Bend files included), and
# site/ (the website: no gate runs on it; `make site-check` is its own
# check). (The other .github/scripts/ files, release/ among them, and
# README.md stay code: eukhe-cli's packaging tests run and copy them.)
GATE_TOOLING = (
    ".github/scripts/ci_*",
    ".github/scripts/test_ci_*",
    ".github/scripts/bend_proofs.py",
    ".github/scripts/test_bend_proofs.py",
)
OUTSIDE_CRATES = (
    ".github/*", "nix/*", "spec/*", ".config/nextest.toml", "mise.toml",
    ".pre-commit-config.yaml", ".gitleaks.toml", "AGENTS.md",
    "Makefile", "flake.nix", "flake.lock",
    "LAWS.bend", "PROOF.bend", "LAWS.lock", "laws/*", "proof/*", "site/*",
)


def outside_crates(path: str) -> bool:
    if any(fnmatchcase(path, pattern) for pattern in GATE_TOOLING):
        return True
    if fnmatchcase(path, ".github/scripts/*"):
        return False
    return path == "" or any(fnmatchcase(path, pattern) for pattern in OUTSIDE_CRATES)


# A change the proofs gate must check: a Bend file, the generated core and
# its entry list, or the scripts and toolchain pin the gate runs. The Bend
# files of site/ are the website's (its own laws and proofs, `make
# site-check`): no gate checks them.
BEND_INPUTS = (
    "*.bend", "bend/*", "crates/eukhe-bend/*",
    ".github/scripts/bend_core.py", ".github/scripts/bend_proofs.py",
    ".github/scripts/check_laws_wired.py", ".github/scripts/pinned_bend.py",
    ".github/scripts/toolchain.env", ".github/scripts/toolchain.py",
)


def select_crates(rows: Rows) -> list[str]:
    """The crates a change touches and their reverse dependencies
    (.github/scripts/ci_pr_crates.py), as cargo arguments: `-p <crate>` each,
    or `--workspace` for another path outside crates/<crate>/. Empty for no
    change, a docs-only change, or paths no crate builds or tests from."""
    if not rows:
        print("no change")
        return []
    if docs_only([path for row in rows for path in row]):
        print("docs-only change (Markdown at the root)")
        return []
    kept = [(path, old) for path, old in rows if not (outside_crates(path) and outside_crates(old))]
    if not kept:
        print("no crate builds or tests from the changed paths")
        return []
    crates = ci_pr_crates.select_crates(kept)
    ci_pr_crates.write_outputs(crates, "/dev/null")
    if not crates:
        return ["--workspace"]
    return [arg for crate in crates for arg in ("-p", crate)]


def clippy_touched(rows: Rows) -> None:
    selected = select_crates(rows)
    if not selected:
        print("clippy skipped")
        return
    run("cargo", "clippy", *selected, "--all-targets", "--locked", "--", "-D", "warnings")


def unit_targets(selected: list[str]) -> list[str]:
    """The cargo target arguments of the unit tests of the packages
    `selected` names: --lib, --bins, and --test for each integration test
    target that is not an e2e suite (named *_e2e, .config/nextest.toml). The
    e2e binaries that pre-push does not run are not built either."""
    want = {arg for arg in selected if arg not in ("-p", "--workspace")}
    metadata = json.loads(output("cargo", "metadata", "--no-deps", "--format-version", "1", "--locked"))
    targets = ["--lib", "--bins"]
    for package in metadata["packages"]:
        if want and package["name"] not in want:
            continue
        for target in package["targets"]:
            if "test" in target["kind"] and target.get("test", True) and not target["name"].endswith("_e2e"):
                targets += ["--test", target["name"]]
    return targets


def tests_touched(rows: Rows) -> None:
    selected = select_crates(rows)
    if not selected:
        print("tests skipped")
        return
    run(
        "cargo", "nextest", "run", *selected, *unit_targets(selected),
        "--locked", "--profile", "pre-push", "--no-tests=pass",
        env=clean_env(),
    )


def embedded_js(rows: Rows) -> None:
    """The embedded JavaScript against its TypeScript sources (`make
    embedded-js-check`: crates/eukhe-dashboard/ui/scripts/embedded-js.ts),
    when a change touches a .ts or .js file under crates/, a tsconfig.json
    there, or the dashboard UI's locked packages (the generator's tools)."""
    sources = ("crates/*.ts", "crates/*.js", "crates/*/tsconfig.json", "crates/eukhe-dashboard/ui/package-lock.json")
    if not touched(rows, sources):
        print("embedded js skipped: no TypeScript source or generated file changed")
        return
    make("embedded-js-check")


def proofs(rows: Rows, base: str) -> None:
    """The proofs a Bend change can reach (.github/scripts/bend_proofs.py:
    the proof files whose import closure holds a changed file), from the
    commit `base`."""
    if not touched(rows, BEND_INPUTS, skip=("site/*",)):
        print("proofs skipped: no Bend input changed")
        return
    run("python3", ".github/scripts/check_laws_wired.py", ".")
    run("python3", ".github/scripts/bend_core.py", "check")
    run("python3", ".github/scripts/bend_proofs.py", "--base", base)


# The laws against the committed LAWS.lock (the bend skill's `gate.py
# --lock-only`, seconds), when a law, a spec helper, the lock or the skill
# pin changed: a law changed without the user's re-lock fails here.
# BEND_SKILL: the skill directory (default: the commit BEND_SKILL_REV of
# .github/scripts/toolchain.env, .github/scripts/pinned_skill.py).
# LOCK_FLAGS: what the lock freezes depends on them; `make lock` passes them
# and the lock keeps them, so a bare `gate.py . --lock-only` checks the same
# way, and the check here passes them too (other ones are an ERROR)
# (`--code 'bend/*'`: the defs under bend/ are the code, every def a law
# reaches outside it is a spec helper and frozen; `--freeze`: every doc and
# every .bend file under spec/, byte for byte).
LOCK_FLAGS = ("--code", "bend/*", "--freeze", "spec/**/*.md", "--freeze", "spec/**/*.bend")
LOCK_INPUTS = (
    "LAWS.bend", "LAWS.lock", "laws/*", "spec/*",
    ".github/scripts/pinned_skill.py", ".github/scripts/toolchain.env", ".github/scripts/toolchain.py",
)


def bend_skill() -> str:
    if os.environ.get("BEND_SKILL"):
        return os.environ["BEND_SKILL"]
    try:
        return str(pinned_skill.skill_dir())
    except pinned_skill.Unpinned as error:
        print(error, file=sys.stderr)
        raise Failed(1) from None


def laws_lock(rows: Rows) -> None:
    if not touched(rows, LOCK_INPUTS):
        print("lock skipped: no law or lock changed")
        return
    run("python3", f"{bend_skill()}/scripts/gate.py", ".", "--lock-only", *LOCK_FLAGS)


def relock() -> None:
    """`make lock`: the proofs the change since origin/main can reach
    (.github/scripts/bend_proofs.py), then LAWS.lock written from the laws
    (`gate.py --lock-only --lock`: no checker run). The nightly gate proves
    everything and runs --verdict."""
    skill = bend_skill()
    run("python3", ".github/scripts/check_laws_wired.py", ".")
    run("python3", ".github/scripts/bend_proofs.py", "--base", output("git", "merge-base", "HEAD", "origin/main"))
    run("python3", f"{skill}/scripts/gate.py", ".", "--lock-only", "--lock", *LOCK_FLAGS)


def secrets_staged() -> None:
    if shutil.which("gitleaks") is None:
        print("gitleaks is not installed: the staged diff is not scanned (the pre-push gate scans the pushed commits)")
        return
    run("gitleaks", "git", "--pre-commit", "--staged", "--redact", "--no-banner", "--config", ".gitleaks.toml", ".")


def secrets_range(log_range: str) -> None:
    check_tools("gitleaks")
    print(f"scanning: {log_range}")
    run("gitleaks", "git", "--redact", "--no-banner", "--config", ".gitleaks.toml", f"--log-opts={log_range}", ".")


def tee(*args: str) -> str:
    """Run the command with its stdout printed as it comes and returned."""
    with subprocess.Popen(args, stdout=subprocess.PIPE, text=True, errors="replace") as process:
        lines = []
        for line in process.stdout:
            sys.stdout.write(line)
            lines.append(line)
    if process.returncode:
        raise Failed(exit_code(process.returncode))
    return "".join(lines)


def proved(out: str) -> None:
    if "ALL PROOFS CHECK" not in out.split("\n"):
        raise Failed(1)


def laws() -> None:
    run("python3", ".github/scripts/check_laws_wired.py", ".")
    run("python3", ".github/scripts/bend_core.py", "check")
    proved(tee("bend", "PROOF.bend"))
    proved(tee("bend", "PROOF.bend", "--verdict"))


def dashboard_ui() -> None:
    make("dashboard-ui")
    run("git", "diff", "--exit-code", "--stat", "--", "crates/eukhe-dashboard/web")
    if output("git", "status", "--porcelain", "--", "crates/eukhe-dashboard/web"):
        raise Failed(1)


def dashboard_ui_changed(rows: Rows) -> None:
    """The dashboard UI gate of full (format, lint, tests, build, and the
    committed web/ matching the build), when a change touches
    crates/eukhe-dashboard/ui/."""
    if not touched(rows, ("crates/eukhe-dashboard/ui/*",)):
        print("dashboard ui skipped: nothing under crates/eukhe-dashboard/ui/ changed")
        return
    dashboard_ui()


def nix_vendor_changed(rows: Rows) -> None:
    """The source build's vendored dependencies (make nix-vendor), when a
    change touches Cargo.lock, the flake or nix/: a git dependency moved
    without its hash in nix/source.nix fails here, not in a user's build."""
    if touched(rows, ("Cargo.lock", "flake.nix", "flake.lock", "nix/*")):
        make("nix-vendor")
        return
    print("nix vendor skipped: Cargo.lock, the flake and nix/ are unchanged")


BUILD_SETTINGS = ("CARGO_*", "RUSTUP_*", "RUSTFLAGS", "RUSTDOCFLAGS", "RUSTC_WRAPPER", "SCCACHE_*")


def clean_env() -> dict[str, str]:
    """The test environment is clean (AGENTS.md: inherited EUKHE_* variables
    would point test daemons at real state), except for the build settings
    (cargo's, rustup's, sccache's; mise.toml), so the tests reuse the build
    the other gates made."""
    env = {
        "HOME": os.environ["HOME"],
        "PATH": os.environ["PATH"],
        "USER": os.environ.get("USER", ""),
        "LANG": os.environ.get("LANG") or "C.UTF-8",
        "BEND_NO_TELEMETRY": "1",
    }
    env.update(
        (name, value)
        for name, value in os.environ.items()
        if any(fnmatchcase(name, pattern) for pattern in BUILD_SETTINGS)
    )
    return env


def workspace_tests() -> None:
    """Every test: nextest profile nightly (every binary at once on one
    build; the e2e suites and the self-serializing tests in their test
    groups, .config/nextest.toml), then the doctests, which nextest does not
    run. The flaky tests (a failure, then a pass on the retry) are named
    from the JUnit report."""
    code = exit_code(
        subprocess.run(["cargo", "nextest", "run", "--workspace", "--locked", "--profile", "nightly"], env=clean_env()).returncode
    )
    junit = Path("target/nextest/nightly/junit.xml")
    if junit.is_file():
        for case in ET.parse(junit).iter("testcase"):
            if case.find("flakyFailure") is not None or case.find("flakyError") is not None:
                print(f"  flaky: {case.get('classname')} {case.get('name')}")
    if code:
        raise Failed(code)
    run("cargo", "test", "--workspace", "--doc", "--locked", env=clean_env())


def sdk_ts() -> None:
    """The TypeScript SDK (`make sdk-ts`) in the tests' clean environment:
    its e2e starts eukhe agents, which an inherited EUKHE_* would point at
    real state. After the tests: the eukhe it builds reuses their build."""
    run("make", "--no-print-directory", "sdk-ts", env=clean_env())


def side_lane() -> None:
    gate("secrets", secrets_range, os.environ.get("CI_LOCAL_SECRETS_RANGE") or "origin/main..HEAD")
    gate("deny", make, "deny")
    gate("laws", laws)
    gate("runtime-test", make, "runtime-test")
    gate("nix-test", make, "nix-test")
    gate("nix-vendor", make, "nix-vendor")
    gate("embedded js", make, "embedded-js-check")
    gate("dashboard-ui", dashboard_ui)


def lane(steps) -> int:
    """Run `steps` as one lane: the exit code of its first failed gate, else 0."""
    try:
        steps()
    except SystemExit as stop:
        return stop.code if isinstance(stop.code, int) else 1
    return 0


def rust_lane() -> None:
    gate("clippy", run, "cargo", "clippy", "--workspace", "--all-targets", "--locked", "--", "-D", "warnings")
    gate("test", workspace_tests)
    gate("sdk-ts", sdk_ts)


def full() -> int:
    # The full gate builds the workspace once: incremental files only add
    # size, and a non-incremental build is one sccache keeps (the nightly
    # worktree's path is the same every night). clean_env passes it on.
    os.environ["CARGO_INCREMENTAL"] = "0"
    start = time.monotonic()
    gate("tools", check_tools, "cargo", "cargo-nextest", "uv", "node", "npm", "python3", "cargo-deny", "jq")
    gate("bend version", check_bend)
    gate("lean version", check_lean)
    gate("fmt", run, "cargo", "fmt", "--all", "--check")
    gate("crate layers", run, "python3", ".github/scripts/check_crate_layers.py", ".")
    # The other lane runs in a forked process, its output in a log. The
    # rlm tests send SIGINT, so it takes the default SIGINT action
    # (Ctrl+C then stops every lane). The Rust lane runs in the foreground:
    # its pty tests need the terminal state of a foreground job.
    log = tempfile.TemporaryFile(mode="w+", errors="replace")
    sys.stdout.flush()
    sys.stderr.flush()
    side = os.fork()
    if side == 0:
        code = 1
        try:
            signal.signal(signal.SIGINT, signal.SIG_DFL)
            with open(os.devnull) as devnull:
                os.dup2(devnull.fileno(), 0)
            os.dup2(log.fileno(), 1)
            os.dup2(log.fileno(), 2)
            code = lane(side_lane)
        finally:
            sys.stdout.flush()
            sys.stderr.flush()
            os._exit(code)
    rust_code = lane(rust_lane)
    side_code = exit_code(os.waitstatus_to_exitcode(os.waitpid(side, 0)[1]))
    print("==> ci-full: secrets, deny, laws, runtime-test, nix-test, nix-vendor, embedded js, dashboard-ui log")
    log.seek(0)
    shutil.copyfileobj(log, sys.stdout)
    log.close()
    print(f"ci-full: {int(time.monotonic() - start)}s")
    if rust_code or side_code:
        print("ci-full: FAILED (the failed gates are named above)", file=sys.stderr)
        return 1
    print("ci-full: every gate passed")
    return 0


def pre_push() -> int:
    to = os.environ.get("PRE_COMMIT_TO_REF")
    if not to:
        print("PRE_COMMIT_TO_REF is unset: prek gives it in the pre-push hook", file=sys.stderr)
        return 1
    start = os.environ.get("PRE_COMMIT_FROM_REF", "")
    for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"):
        os.environ.pop(name, None)
    # The gates check this worktree, so it must be the pushed commit.
    pushed = subprocess.run(["git", "rev-parse", f"{to}^{{commit}}"], stdout=subprocess.PIPE, text=True).stdout.strip()
    if output("git", "rev-parse", "HEAD") != pushed:
        head = output("git", "rev-parse", "--short=12", "HEAD")
        print(f"pre-push: the push sends {to[:12]}, but this worktree is at {head}. Push from a worktree at the pushed commit.", file=sys.stderr)
        return 1
    if (
        start
        and not re.fullmatch("0+", start)
        and subprocess.run(["git", "cat-file", "-e", f"{start}^{{commit}}"], stderr=subprocess.DEVNULL).returncode == 0
    ):
        base = start
    else:
        base = output("git", "merge-base", to, f"{os.environ.get('PRE_COMMIT_REMOTE_NAME') or 'origin'}/main")
    rows = change_rows(base, to)
    print(f"pre-push: {base[:12]}..{to[:12]}")
    gate("bend version", check_bend)
    gate("fmt", run, "cargo", "fmt", "--all", "--check")
    gate("secrets", secrets_range, f"{base}..{to}")
    # A push to a branch other than main (an integration branch) stops here:
    # main's push runs the rest once, when the branch merges.
    branch = os.environ.get("PRE_COMMIT_REMOTE_BRANCH", "")
    if branch and branch != "refs/heads/main":
        print(f"pre-push: {branch} is not main: clippy, proofs, lock and tests run when it merges into main")
        return 0
    gate("clippy (touched crates)", clippy_touched, rows)
    gate("proofs", proofs, rows, base)
    gate("embedded js", embedded_js, rows)
    gate("dashboard ui", dashboard_ui_changed, rows)
    gate("nix vendor", nix_vendor_changed, rows)
    gate("laws lock", laws_lock, rows)
    gate("tests (touched crates)", tests_touched, rows)
    return 0


def fast() -> int:
    rows = change_rows("--cached")
    gate("bend version", check_bend)
    gate("fmt", run, "cargo", "fmt", "--all", "--check")
    gate("crate layers", run, "python3", ".github/scripts/check_crate_layers.py", ".")
    gate("secrets", secrets_staged)
    gate("embedded js", embedded_js, rows)
    gate("clippy (touched crates)", clippy_touched, rows)
    return 0


def lock() -> int:
    gate("bend version", check_bend)
    gate("relock", relock)
    return 0


def load_mise() -> None:
    """The tools and the build environment of mise.toml, trusted and installed."""
    if not Path("mise.toml").is_file() or shutil.which("mise") is None:
        return
    run("mise", "trust", "--quiet", "mise.toml")
    run("mise", "install", "--quiet")
    os.environ.update(json.loads(output("mise", "env", "--json")))


def main() -> int:
    global MODE
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    if len(sys.argv) < 2 or not sys.argv[1]:
        print(USAGE, file=sys.stderr)
        return 1
    MODE = sys.argv[1]
    modes = {"fast": fast, "pre-push": pre_push, "full": full, "lock": lock}
    if MODE not in modes:
        print(USAGE, file=sys.stderr)
        return 2
    os.chdir(ROOT)
    load_mise()
    os.environ.pop("RUSTUP_TOOLCHAIN", None)
    os.environ["BEND_NO_TELEMETRY"] = "1"
    # The pinned Bend (.github/scripts/pinned_bend.py) leads PATH, and
    # BEND_BIN names it for .github/scripts/bend_core.py and
    # .github/scripts/bend_proofs.py (a mise python3 shim rewrites PATH), so
    # every gate runs it whatever a version manager's default is. check_bend
    # fails, naming the version, without it.
    bend = pinned_bend.find()
    if bend is not None:
        os.environ["PATH"] = f"{os.path.dirname(bend)}:{os.environ['PATH']}"
        os.environ["BEND_BIN"] = bend
    return modes[MODE]()


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Failed as failed:
        raise SystemExit(failed.code) from None
    except KeyboardInterrupt:
        raise SystemExit(130) from None
