#!/usr/bin/env python3
"""bend_proofs.py --base REF [--list]: prove only the laws a change can break.

A proof entry is a file PROOF.bend imports (LAWS.bend aside). Bend reads
nothing but a file's imports (and Base), so a proof can change its verdict
only when a file of its import closure changes. The change is the working
tree against REF: `git diff --name-only REF` (both sides of a rename) plus
the untracked files. The entries whose closure holds a changed file, and
the entries PROOF.bend gained, are the selection. Bend fails a run with a
law left open (`N TODOs found`), and it loads every law of a law module an
entry reads (laws/<area>.bend, LAWS.bend), so the selection grows to every
entry that fills a law of a law module in its closure, until none is
missing. It is written to PROOF_CHANGED.bend (an imports-only index at the
root, beside PROOF.bend, git-ignored), and `bend PROOF_CHANGED.bend` runs
on it. It passes with exit 0 and a stdout line `ALL PROOFS CHECK`.

The closure is exact, so a shared file (laws/base.bend, proof/base/,
bend/wire.bend) selects every proof that reads it and nothing else;
bend/core.bend, which no proof imports, selects none (scripts/bend_core.py
check covers it). The whole PROOF.bend runs instead when the Bend pin
(scripts/toolchain.env) or this script changes, when a line of PROOF.bend or LAWS.bend
other than an import changes, or when half of the entries or more are
selected (one run of everything costs no more than such an index).

--list prints the decision and the selection and runs nothing. The bend
run is --bend, else BEND_BIN (scripts/ci_local.sh sets it to the pinned
release: a version manager's `python3` shim rewrites PATH for this
process, so `bend` on PATH could be another release), else `bend`.

Callers: scripts/ci_local.sh (the pre-push proofs gate, REF = the pushed
range's base) and `make lock` (REF = the merge base with origin/main).
Tests: python3 scripts/test_bend_proofs.py
"""

from __future__ import annotations

import argparse
import functools
import os
import re
import subprocess
import sys
from pathlib import Path

IMPORT = re.compile(r"^import\s+(\S+\.bend)\s+as\s+\S+", re.M)
IMPORT_ALIAS = re.compile(r"^import\s+(\S+\.bend)\s+as\s+(\S+)", re.M)
INDEX = "PROOF_CHANGED.bend"
# How every proof is checked or chosen: a change runs them all.
FULL_PATHS = {"scripts/toolchain.env", "scripts/bend_proofs.py"}


def is_law_module(path: Path, root: Path) -> bool:
    return path == root / "LAWS.bend" or root / "laws" in path.parents


def filled_modules(entry: Path, root: Path) -> set[Path]:
    """The law modules whose laws `entry` fills (`def <its alias>.<law>(`)."""
    try:
        text = entry.read_text(encoding="utf-8")
    except FileNotFoundError:
        return set()
    return {
        (entry.parent / p).resolve()
        for p, alias in IMPORT_ALIAS.findall(text)
        if is_law_module((entry.parent / p).resolve(), root)
        and re.search(rf"^def {re.escape(alias)}\.\w+\(", text, re.M)
    }


@functools.cache
def imports(path: Path) -> list[Path]:
    """The .bend files `path` imports (resolved); none for a missing file."""
    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return []
    return [(path.parent / p).resolve() for p in IMPORT.findall(text)]


def closure(entry: Path, memo: dict[Path, frozenset[Path]]) -> frozenset[Path]:
    """`entry` and every file it imports, transitively."""
    if entry in memo:
        return memo[entry]
    seen: set[Path] = set()
    todo = [entry]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        todo.extend(imports(f))
    memo[entry] = frozenset(seen)
    return memo[entry]


def index_lines(text: str) -> tuple[list[str], list[str]]:
    """An index file's import targets, and its other code lines (comments and
    blank lines dropped)."""
    targets, other = [], []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        m = IMPORT.match(s)
        if m:
            targets.append(m.group(1))
        elif s != "import Base":
            other.append(s)
    return targets, other


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *args], check=True, capture_output=True, text=True
    ).stdout


def at_base(root: Path, base: str, rel: str) -> str:
    r = subprocess.run(
        ["git", "-C", str(root), "show", f"{base}:{rel}"], capture_output=True, text=True
    )
    return r.stdout if r.returncode == 0 else ""


def changed_paths(root: Path, base: str) -> set[str]:
    paths: set[str] = set()
    for line in git(root, "diff", "--name-status", "-M", "--no-color", base).splitlines():
        paths.update(line.split("\t")[1:])
    paths.update(git(root, "ls-files", "--others", "--exclude-standard").splitlines())
    paths.discard(INDEX)
    return paths


def select(root: Path, base: str) -> tuple[str, list[str]]:
    """(why, entries): entries == [] with a `full` why means all of PROOF.bend."""
    root = root.resolve()
    changed = changed_paths(root, base)
    full = sorted(changed & FULL_PATHS)
    if full:
        return f"full: {', '.join(full)} changed", []
    targets, _ = index_lines((root / "PROOF.bend").read_text(encoding="utf-8"))
    entries = [t for t in targets if Path(t).name != "LAWS.bend"]
    for index in ("PROOF.bend", "LAWS.bend"):
        if index in changed:
            _, old_other = index_lines(at_base(root, base, index))
            _, new_other = index_lines((root / index).read_text(encoding="utf-8"))
            if old_other != new_other:
                return f"full: a line of {index} other than an import changed", []
    old_entries = set(index_lines(at_base(root, base, "PROOF.bend"))[0])
    hit = {(root / p).resolve() for p in changed if p.endswith(".bend")}
    memo: dict[Path, frozenset[Path]] = {}
    path = {e: (root / e).resolve() for e in entries}
    chosen = {e for e in entries if e not in old_entries or hit & closure(path[e], memo)}
    if not chosen:
        return "none: no proof reads a changed file", []
    fillers: dict[Path, list[str]] = {}
    for e in entries:
        for m in filled_modules(path[e], root):
            fillers.setdefault(m, []).append(e)
    loaded: set[Path] = set()
    todo = list(chosen)
    while todo:
        laws = {f for f in closure(path[todo.pop()], memo) if is_law_module(f, root)}
        for m in laws - loaded:
            loaded.add(m)
            new = [e for e in fillers.get(m, []) if e not in chosen]
            chosen.update(new)
            todo.extend(new)
    if 2 * len(chosen) >= len(entries):
        return f"full: {len(chosen)} of {len(entries)} proof files", []
    return f"{len(chosen)} of {len(entries)} proof files", [e for e in entries if e in chosen]


def run(root: Path, bend: str, main: str) -> int:
    print(f"bend {main}", flush=True)
    r = subprocess.run([bend, main], cwd=root, stdout=subprocess.PIPE, text=True)
    sys.stdout.write(r.stdout)
    ok = r.returncode == 0 and "ALL PROOFS CHECK" in r.stdout.splitlines()
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--base", required=True, help="the commit the change starts from")
    ap.add_argument("--root", default=".", help="the repository root (default: .)")
    ap.add_argument(
        "--bend",
        default=os.environ.get("BEND_BIN") or "bend",
        help="the bend executable (default: $BEND_BIN, else bend on PATH)",
    )
    ap.add_argument("--list", action="store_true", help="print the selection, run nothing")
    args = ap.parse_args()
    root = Path(args.root).resolve()
    why, chosen = select(root, args.base)
    print(f"proofs: {why}")
    for e in chosen:
        print(f"  {e}")
    if args.list or why.startswith("none"):
        return 0
    if not chosen:
        return run(root, args.bend, "PROOF.bend")
    body = "".join(f"import {e} as P{k}\n" for k, e in enumerate(chosen))
    (root / INDEX).write_text(
        f"# {INDEX}: the proofs of one change (scripts/bend_proofs.py; not committed).\n\n"
        f"import Base\n{body}",
        encoding="utf-8",
    )
    return run(root, args.bend, INDEX)


if __name__ == "__main__":
    sys.exit(main())
