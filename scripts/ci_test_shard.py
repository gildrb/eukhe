#!/usr/bin/env python3
"""Stable-hash test sharding for the local test gate (scripts/ci_local.sh).

`cargo test --workspace` runs every test binary one after another. The
local full gate (`make ci-local`, the nightly gate) runs the shards of this
script at the same time on one build instead. This script enumerates the
workspace's test units the same way cargo does (via `cargo metadata
--no-deps`, no build) and runs the subset assigned to one shard of N by a
STABLE hash: every unit id is mapped with crc32(unit) % N, so a unit lands
in exactly one shard on every run - binaries never move between shards
when the suite grows or shrinks, keeping flake attribution stable.

Unit kinds (the exact set `cargo test --workspace` builds and runs; every
target honors its manifest `test` flag exactly as cargo does, so a target
with `test = false` is never run here either):
  lib   — package lib unittests            (`cargo test -p PKG --lib`)
  bin   — package bin unittests            (`cargo test -p PKG --bin NAME`)
  test  — tests/ integration target        (`cargo test -p PKG --test NAME`)
  doc   — package doctests                 (`cargo test -p PKG --doc`)
  example — example target with `test = true`: `cargo test --workspace`
          also runs its example tests, so each one is its own unit
          (`cargo test -p PKG --example NAME`)
  examples — compile parity target: `cargo test --workspace` builds every
          example without running it; the owning shard reproduces exactly
          that with `--examples --no-run`.
  Bench targets are NOT enumerated: cargo test's default selection never
  builds them (the Cargo book lists lib, bins, examples, and test targets
  only), so a bench — e.g. a nightly-only `#[bench]` — must not gate what
  the serial gate never compiled.

Every unit is recorded in the shard manifest (JSON) that
scripts/ci_test_shard_summary.py audits: the union of shard manifests must
equal the full enumeration, so coverage can never silently regress when
targets are added or renamed. Output streams live to the log.

lib, bin, test and example units run the executable that `cargo test
--workspace --no-run --message-format=json` built (`--artifacts`, the
JSON lines), in the package directory with CARGO_MANIFEST_DIR set, as cargo
test runs it. They never run `cargo test -p PKG`: that resolves the
features of one package, not of the workspace, so it relinks shared
binaries (target/debug/eukhe) with other features while the other shards
execute them (ETXTBSY), and the tests would run another build than the
workspace one. doc and examples units still run `cargo test -p PKG`: they
build no binary another unit executes.

`--crates a,b` narrows the selection, never the partition: it restricts the
units a run executes to the named packages'. The stable crc32 assignment is
untouched - a unit still lands in exactly one shard of N - so the narrow and
full runs of a unit are the same shard. Every shard records the selection
scope in its manifest, and the summary audits the union against the
SELECTED set: a narrowed run can never pass as a full one.

Usage (from the repo root; scripts/ci_local.sh runs it):

  python3 scripts/ci_test_shard.py --shard 2 --total 8 \
      --manifest shard-manifest.json
  python3 scripts/ci_test_shard.py --list   # enumerate + shard assignment
  python3 scripts/ci_test_shard.py --shard 2 --total 8 --crates eukhe-tui \
      --print-selection   # resolve + report the selection, run nothing
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import zlib
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
# `cargo test --workspace` builds every example to prove it compiles but
# never runs it; the owning shard repeats the same build-only contract.
COMPILE_ONLY_KINDS = ("examples",)


def _target_flag(kind: str, name: str | None) -> list[str]:
    if kind == "lib":
        return ["--lib"]
    if kind == "bin":
        return ["--bin", name or ""]
    if kind == "test":
        return ["--test", name or ""]
    if kind == "doc":
        return ["--doc"]
    if kind == "example":
        return ["--example", name or ""]
    if kind in COMPILE_ONLY_KINDS:
        return [f"--{kind}", "--no-run"]
    raise ValueError(f"unknown unit kind {kind!r}")


def _unit_id(package: str, kind: str, name: str | None) -> str:
    if kind in COMPILE_ONLY_KINDS or kind == "doc":
        return f"{package}#{kind}"
    return f"{package}#{kind}:{name}"


def shard_of(unit_id: str, total: int) -> int:
    return zlib.crc32(unit_id.encode("utf-8")) % total


def _unit_package(unit_id: str) -> str:
    return unit_id.split("#", 1)[0]


def enumerate_units() -> list[dict]:
    """The workspace's test units, exactly what `cargo test --workspace` covers.

    `cargo metadata --no-deps` reads the manifests without building; targets
    carry the same test/doctest flags cargo honors, so this enumeration is
    byte-identical to what the serial workspace test would build and run.
    """
    out = subprocess.run(
        ["cargo", "metadata", "--format-version", "1", "--locked", "--no-deps"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
    )
    packages = json.loads(out.stdout)["packages"]
    units = []
    manifest_of = {pkg["name"]: pkg["manifest_path"] for pkg in packages}
    for pkg in packages:
        name = pkg["name"]
        has_examples = False
        for target in pkg["targets"]:
            kinds = target["kind"]
            tname = target["name"]
            if ("lib" in kinds or "proc-macro" in kinds) and target.get("test", True):
                units.append({"package": name, "kind": "lib", "name": tname})
            if "bin" in kinds and target.get("test", True):
                units.append({"package": name, "kind": "bin", "name": tname})
            if "test" in kinds and target.get("test", True):
                units.append({"package": name, "kind": "test", "name": tname})
            if "example" in kinds:
                has_examples = True
                if target.get("test", False):
                    # `cargo test --workspace` runs the tests of examples
                    # with `test = true`; they are real test units here too.
                    units.append({"package": name, "kind": "example",
                                  "name": tname})
            # bench targets: cargo test never selects them by default —
            # deliberately NOT enumerated (see the module docstring).
        # Doc tests: one cargo `--doc` run covers every doctest=true target of
        # the package (lib and bins alike), matching the workspace behavior.
        if any(t.get("doctest", False) for t in pkg["targets"]):
            units.append({"package": name, "kind": "doc", "name": None})
        if has_examples:
            units.append({"package": name, "kind": "examples", "name": None})
    for unit in units:
        unit["id"] = _unit_id(unit["package"], unit["kind"], unit["name"])
        unit["target_args"] = _target_flag(unit["kind"], unit["name"])
        unit["manifest_path"] = manifest_of[unit["package"]]
    return sorted(units, key=lambda u: u["id"])


# The unit kinds that run a prebuilt executable (the cargo artifact's
# target kind for each).
EXECUTABLE_KINDS = {"lib": ("lib", "rlib", "proc-macro"), "bin": ("bin",),
                    "test": ("test",), "example": ("example",)}


def load_executables(path: Path) -> dict[tuple[str, str, str], str]:
    """(manifest path, target kind, target name) -> the test executable.

    `path` holds the JSON lines of `cargo test --workspace --no-run
    --message-format=json`; a test artifact names its executable.
    """
    executables = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("{"):
            continue
        message = json.loads(line)
        if message.get("reason") != "compiler-artifact" or not message.get("executable"):
            continue
        if not message["profile"]["test"]:
            continue
        target = message["target"]
        for kind in target["kind"]:
            executables[(message["manifest_path"], kind, target["name"])] = message["executable"]
    return executables


def unit_command(unit: dict, executables: dict[tuple[str, str, str], str]) -> tuple[list[str], Path, dict]:
    """The command, working directory and extra environment of one unit."""
    if unit["kind"] not in EXECUTABLE_KINDS:
        return (["cargo", "test", "--locked", "-p", unit["package"], *unit["target_args"]],
                REPO_ROOT, {})
    for kind in EXECUTABLE_KINDS[unit["kind"]]:
        exe = executables.get((unit["manifest_path"], kind, unit["name"]))
        if exe is not None:
            package_dir = Path(unit["manifest_path"]).parent
            return ([exe], package_dir, {"CARGO_MANIFEST_DIR": str(package_dir),
                                         "CARGO_PKG_NAME": unit["package"]})
    raise SystemExit(f"no prebuilt test executable for {unit['id']} in --artifacts "
                     "(run cargo test --workspace --no-run --message-format=json first)")


def run_unit(unit: dict, executables: dict[tuple[str, str, str], str]) -> dict:
    cmd, cwd, extra_env = unit_command(unit, executables)
    start = time.monotonic()
    # Streaming (not capture-then-print) so a hung binary is attributable from
    # the live log: the unit header is printed before the invocation starts.
    proc = subprocess.Popen(
        cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, errors="replace", env={**os.environ, **extra_env},
    )
    output_lines = []
    assert proc.stdout is not None
    for raw in proc.stdout:
        print(raw, end="")
        output_lines.append(raw.rstrip("\n"))
    rc = proc.wait()
    result = dict(unit)
    result["rc"] = rc
    result["seconds"] = round(time.monotonic() - start, 1)
    result["failed_tests"] = _failed_tests(output_lines)
    return result


def _failed_tests(lines: list[str]) -> list[str]:
    """Test names cargo lists under the `failures:` blocks of a red binary.

    The harness prints a `failures:` section header before the per-test
    stdout dumps and then the closing `failures:` block with the name list;
    every block is scanned, so the closing list is always found.
    """
    names, in_block = [], False
    for line in lines:
        if line.strip() == "failures:" and not in_block:
            in_block = True
            continue
        if not in_block:
            continue
        if not line.strip():
            continue  # blank lines sit around the failure name list
        if line.startswith("    ") and not line.lstrip().startswith("..."):
            names.append(line.strip())
        else:
            in_block = False  # a stdout dump or result line closes the block
    return list(dict.fromkeys(names))


def write_manifest(path: Path, shard: int, total: int, all_ids: list[str],
                   results: list[dict], crates: list[str] | None = None) -> None:
    selection_ids = [i for i in all_ids
                     if crates is None or _unit_package(i) in set(crates)]
    manifest = {
        "schema": 1,
        "shard": shard,
        "total": total,
        "all_unit_ids": all_ids,
        "digest": hashlib.sha256("\n".join(all_ids).encode("utf-8")).hexdigest(),
        "scope": scope_manifest(crates),
        "selected_unit_ids": selection_ids,
        "units": results,
        # Complete means: every unit this run SELECTED for this shard ran.
        "complete": len(results) == sum(1 for i in selection_ids
                                        if shard_of(i, total) == shard - 1),
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(manifest, indent=1) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def parse_crates(raw: str | None) -> list[str] | None:
    """The selection scope: None = the full union; a crate list narrows it."""
    if raw is None or not raw.strip():
        return None
    crates = sorted({name.strip() for name in raw.split(",") if name.strip()})
    return crates or None


def scope_manifest(crates: list[str] | None) -> dict:
    """The manifest's scope record (the summary audits against it)."""
    if crates is None:
        return {"kind": "all"}
    return {"kind": "crates", "crates": crates}


def selected_units(units: list[dict], crates: list[str] | None) -> list[dict]:
    """The units this run executes: the full union, or the named crates' subset."""
    if crates is None:
        return units
    return [u for u in units if u["package"] in set(crates)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--shard", type=int, required=True, help="1-based shard index")
    parser.add_argument("--total", type=int, required=True, help="shard count")
    parser.add_argument("--artifacts", type=Path, default=None,
                        help="the JSON lines of `cargo test --workspace --no-run "
                             "--message-format=json`: the test executables to run")
    parser.add_argument("--manifest", type=Path, default=None,
                        help="write the per-shard JSON manifest here")
    parser.add_argument("--crates", default=None,
                        help="comma-separated crate names to run (a narrowed "
                             "selection); omit for the full union")
    parser.add_argument("--print-selection", action="store_true",
                        help="resolve + report this shard's selection and its "
                             "units count, run nothing")
    parser.add_argument("--list", action="store_true",
                        help="print the enumeration and shard assignment, run nothing")
    args = parser.parse_args()
    if not 1 <= args.shard <= args.total:
        parser.error("--shard must be in 1..--total")
    crates = parse_crates(args.crates)
    if crates is not None and args.list:
        parser.error("--list enumerates the full workspace; it takes no --crates")

    units = enumerate_units()
    if crates is not None:
        # Fail closed on a mapping bug: a named package the workspace does
        # not build would narrow the run to a silent zero (the selection
        # cannot name what the enumeration never saw).
        known = {u["package"] for u in units}
        unknown = sorted(set(crates) - known)
        if unknown:
            parser.error(
                f"--crates names packages the workspace does not build: "
                f"{', '.join(unknown)} (known: {', '.join(sorted(known))})")
    all_ids = [u["id"] for u in units]
    selection = selected_units(units, crates)
    mine = [u for u in selection if shard_of(u["id"], args.total) == args.shard - 1]
    if crates is None:
        print(f"[shard {args.shard}/{args.total}] {len(mine)}/{len(units)} units "
              "(full selection)")
    else:
        print(f"[shard {args.shard}/{args.total}] {len(mine)}/{len(selection)} units "
              f"(crate selection: {', '.join(crates)}; the full union is {len(units)})")

    if args.print_selection:
        for u in mine:
            print(f"  selected: {u['id']}")
        # One machine line: the selected units count.
        print(f"SELECTED={len(mine)}")
        return 0

    if args.list:
        for u in units:
            print(f"  shard {shard_of(u['id'], args.total) + 1}: {u['id']}")
        return 0

    if args.artifacts is None:
        parser.error("running units needs --artifacts")
    executables = load_executables(args.artifacts)
    results = []
    for u in mine:
        cmd, _, _ = unit_command(u, executables)
        print(f"[shard {args.shard}/{args.total}] RUN {u['id']} ({' '.join(cmd)})")
        result = run_unit(u, executables)
        verdict = "PASS" if result["rc"] == 0 else f"FAIL rc={result['rc']}"
        print(f"[shard {args.shard}/{args.total}] {verdict} {u['id']} "
              f"in {result['seconds']}s")
        results.append(result)
        if args.manifest:
            write_manifest(args.manifest, args.shard, args.total, all_ids,
                           results, crates)

    if args.manifest:
        write_manifest(args.manifest, args.shard, args.total, all_ids,
                       results, crates)

    failed = [r["id"] for r in results if r["rc"] != 0]
    if failed:
        print(f"[shard {args.shard}/{args.total}] FAILED UNITS: {', '.join(failed)}")
        return 1
    print(f"[shard {args.shard}/{args.total}] all {len(results)} units green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
