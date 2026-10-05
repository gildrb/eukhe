#!/usr/bin/env python3
"""Verify an assembled release tarball (host build) end to end.

The local mirror of the eukhe-release.yml build-job gates:
the archive must contain exactly the designed payload at the tarball root,
checksums must match SHA256SUMS and manifest.json, and the staged binary must
report the release version from a scratch cwd with `EUKHE_PACKAGE_DIR` unset
(the shipped artifact never depends on it).

Usage:
    python3 scripts/release/verify_release.py \
        --dist-dir <dir> --version <x.y.z> --target <triple>
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

# The bundled-catalog gate (same release-scripts directory).
from bundle_catalog import validate_bundled_catalog_dir
# The payload layout, target aliases, and shipped-content policy live with
# the assembler (same release-scripts directory).
from assemble_artifacts import (
    BINARY_NAME,
    TARGET_ALIASES,
    RUNTIME_EXCLUDED_NAMES,
    RUNTIME_EXCLUDED_SUFFIXES,
    STAGED_ENTRIES,
)
from runtime_lock import RUNTIME_LOCK_FILE, LockError, parse_requirements

# The designed tarball-root payload (STAGED_ENTRIES in assemble_artifacts.py).
# The bundled catalog assets among them must also pass the same validation
# gates the packer enforced at assembly time.
EXPECTED_TOP_LEVEL = set(STAGED_ENTRIES)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


def top_level_members(archive: tarfile.TarFile) -> set:
    return {
        member.name.split("/", maxsplit=1)[0]
        for member in archive.getmembers()
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dist-dir", required=True, type=Path)
    parser.add_argument("--version", required=True)
    parser.add_argument("--target", required=True)
    args = parser.parse_args()
    if args.target not in TARGET_ALIASES:
        fail(f"unknown release target {args.target!r} (known: {', '.join(TARGET_ALIASES)})")

    archive_name = (
        f"eukhe-{args.version}-{TARGET_ALIASES[args.target]}.tar.gz"
    )
    archive = args.dist_dir / archive_name
    if not archive.is_file():
        fail(f"archive {archive} not found; run assemble_artifacts.py first")

    # 1. Deterministic tarball shape: exact top-level payload, no link entries.
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        if top_level_members(tar) != EXPECTED_TOP_LEVEL:
            fail(
                f"tarball top-level entries {sorted(top_level_members(tar))} "
                f"!= designed payload {sorted(EXPECTED_TOP_LEVEL)}"
            )
        for member in members:
            if member.name.startswith(("skills/", "eukhe-runtime/")) and any(
                part in RUNTIME_EXCLUDED_NAMES or part.endswith(RUNTIME_EXCLUDED_SUFFIXES)
                for part in Path(member.name).parts
            ):
                fail(f"tarball contains a development cache entry {member.name!r}")
            if member.issym() or member.islnk():
                fail(f"tarball contains a link entry {member.name!r}")
            if member.uid != 0 or member.gid != 0 or member.mtime != 0:
                fail(f"tarball entry {member.name!r} is not deterministic "
                     f"(uid={member.uid} gid={member.gid} mtime={member.mtime})")
        # The kernel venv bootstrap installs only this hash-locked file.
        lock_member = f"eukhe-runtime/{RUNTIME_LOCK_FILE}"
        if lock_member not in {member.name for member in members}:
            fail(f"tarball is missing the kernel runtime lock {lock_member!r}")
        lock_file = tar.extractfile(lock_member)
        if lock_file is None:
            fail(f"kernel runtime lock {lock_member!r} is not a regular file")
        with lock_file:
            try:
                parse_requirements(lock_file.read().decode("utf-8"))
            except LockError as error:
                fail(f"kernel runtime lock {lock_member!r} rejected: {error}")

    # 2. Checksums agree with SHA256SUMS and manifest.json.
    archive_sha = sha256_file(archive)
    sums_path = args.dist_dir / "SHA256SUMS"
    sums = {
        Path(name.strip()).name: digest.strip()
        for digest, name in
        (line.split(None, 1) for line in sums_path.read_text().splitlines() if line.strip())
    }
    if sums.get(archive_name) != archive_sha:
        fail(f"SHA256SUMS mismatch for {archive_name}")
    manifest = json.loads((args.dist_dir / "manifest.json").read_text())
    entries = {b["file"]: b for b in manifest["binaries"]}
    if archive_name not in entries:
        fail(f"manifest.json has no entry for {archive_name}")
    if entries[archive_name]["sha256"] != archive_sha:
        fail(f"manifest.json sha256 mismatch for {archive_name}")

    # 3. The staged binary reports the release version from a scratch cwd with
    #    EUKHE_PACKAGE_DIR unset: shipped artifacts never depend on it.
    scratch = Path(tempfile.mkdtemp(prefix="eukhe-verify-"))
    try:
        # Manual extraction: every member must be a plain file or directory
        # whose relative name stays inside scratch, checked before any write;
        # staying on explicit member writes keeps the gate working on any
        # Python >= 3.8 (no `filter=` kwarg).
        scratch_root = str(scratch.resolve())
        with tarfile.open(archive) as tar:
            for member in tar.getmembers():
                name = PurePosixPath(member.name)
                if name.is_absolute() or ".." in name.parts:
                    fail(f"tarball entry {member.name!r} is not a relative in-tree path")
                if not (member.isdir() or member.isfile()):
                    fail(f"tarball entry {member.name!r} is not a regular file or directory")
                target = scratch / member.name
                if os.path.commonpath([scratch_root, str(target.resolve())]) != scratch_root:
                    fail(f"tarball entry {member.name!r} escapes the extraction directory")
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    source = tar.extractfile(member)
                    if source is None:
                        fail(f"tarball entry {member.name!r} has no file data")
                    with source, open(target, "wb") as sink:
                        shutil.copyfileobj(source, sink)
                    os.chmod(target, member.mode & 0o755)
        # The bundled catalog assets must be present and valid in the
        # installed layout (the full packer gates: no small-fixture waiver).
        catalog_facts = validate_bundled_catalog_dir(scratch)
        binary = scratch / BINARY_NAME
        if not os.access(binary, os.X_OK):
            fail(f"staged {BINARY_NAME} is not executable")
        if entries[archive_name]["executableSha256"] != sha256_file(binary):
            fail("executableSha256 in manifest.json does not match the staged binary")
        env = {k: v for k, v in os.environ.items() if k != "EUKHE_PACKAGE_DIR"}
        run = subprocess.run(
            [str(binary), "--version"],
            capture_output=True, text=True, env=env, cwd=scratch, check=False,
        )
        if run.returncode != 0:
            fail(f"staged eukhe --version failed: {run.stderr.strip()}")
        version_out = run.stdout.strip()
        if version_out != args.version:
            fail(
                f"staged eukhe reports {version_out!r}, "
                f"expected {args.version!r}"
            )
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    print(
        f"verified {archive_name}: payload, checksums, manifest, "
        f"catalog assets ({json.dumps(catalog_facts)}), livecheck all OK"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
