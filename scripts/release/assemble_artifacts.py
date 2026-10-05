#!/usr/bin/env python3
"""Assemble eukhe release tarballs.

The per-target packaging step of `.github/workflows/eukhe-release.yml`: stage
the release binary plus the bundled kernel runtime, skills, and license
metadata into a scratch tree, pack a deterministic tarball with files at the
tarball root, and emit `SHA256SUMS` plus a `manifest.json` (archive sha256,
executable sha256, platform alias, target triple, Linux decoder facts).

Usage:
    python3 scripts/release/assemble_artifacts.py \
        --repo-root <repo> --version <x.y.z> --target <triple> \
        [--binary <path>] [--decoder <path>] [--runtime-dir <dir>] \
        [--out-dir <dir>] [--catalog-assets <dir>]

`--catalog-assets` is the directory holding the generated bundled catalog
assets (`models.bundled.json` + `mcp-services.bundled.json`); the packer
hard-fails without VALIDATED assets (version gates + >= 42 transport tuples +
>= 68 services — see scripts/release/bundle_catalog.py, the catalog spec §3.2
no-cold-start layer 2). The release workflow fetches the catalog commit pinned
in catalog-pin.json (`bundle_catalog.py generate --network`, sha256-checked);
the Nix source build copies the repository's catalog snapshot (`--catalog-dir`).

`--binary` defaults to `<repo>/target/<target>/release/eukhe` (cross builds)
and falls back to `<repo>/target/release/eukhe` (host builds).
`--decoder` is the split-debug sidecar from split_debug.py, required (with an
explicit `--binary`) on Linux targets and rejected elsewhere.
`--runtime-dir` defaults to `<repo>/eukhe-runtime` (the vendored sidecar
from the kernel-packaging lane).

Archive naming: `eukhe-<version>-<platform-alias>.tar.gz` (e.g.
`eukhe-0.1.0-linux-x64.tar.gz`) — the asset name the release workflow
publishes and records per Nix system in `nix/release.json`, whose tarball
layout `nix/package.nix` installs. The target triple stays in the manifest
entry's `target` field (provenance, SBOM keying).
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

# The bundled-catalog validation gate (same release-scripts directory).
from bundle_catalog import BUNDLED_CATALOG_FILES, validate_bundled_catalog_dir
from runtime_lock import LockError, read_runtime_lock

# Tarball-root payload: the exe-adjacent layout the binary resolves at
# runtime, and the one `nix/package.nix` copies into its payload directory.
BINARY_NAME = "eukhe"
STAGED_ENTRIES = [
    BINARY_NAME,
    "eukhe-runtime",
    "skills",
    "LICENSE",
    "README.md",
    # The bundled catalog assets (spec §3.2 layer 2): staged at the tarball
    # root beside the binary — the runtime resolves <packageDir>/<name>.
    "models.bundled.json",
    "mcp-services.bundled.json",
]


# Shipped-content policy: what the installed tree carries beyond the binary.
#
# The runtime sidecar ships only what the kernel consumes. The venv
# bootstrap installs `<payload>/eukhe-runtime/requirements-kernel.txt`
# (`uv pip install --require-hashes --only-binary :all:`, the hash-locked
# export of `uv.lock`; runtime_lock.py gates it at staging), then the
# runtime itself with `--no-deps --no-index --no-build-isolation` (the
# hatchling wheel targets only `src/rlm`). The venv cache identity hashes
# `src/rlm/*.py` + the packaged machine library under `src/rlm/machines` +
# `pyproject.toml` + the requirements lock — so the pytest suite (`test/`)
# and the development `uv.lock` (already exported into the requirements
# lock) are dead weight in every installed tree, and dropping them changes
# neither the built wheel nor the bootstrap-version identity. The cache
# names and suffixes mirror package_release.py's EXCLUDED_* so a stale
# `.venv` or `__pycache__` cannot ride the payload either.
RUNTIME_EXCLUDED_NAMES = frozenset({
    "test",
    "uv.lock",
    ".venv",
    "__pycache__",
    ".pytest_cache",
    ".ruff_cache",
    ".mypy_cache",
    ".git",
    ".DS_Store",
    "node_modules",
})
RUNTIME_EXCLUDED_SUFFIXES = (".pyc", ".egg-info")

# Rust target triple -> release platform alias (the archive-name suffix and
# the manifest's `platform` field). Exactly the eukhe-release.yml matrix.
TARGET_ALIASES = {
    "x86_64-unknown-linux-gnu": "linux-x64",
    "aarch64-unknown-linux-gnu": "linux-arm64",
    "aarch64-apple-darwin": "darwin-arm64",
}

VERSION_RE = re.compile(r"^\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?$")

# Split-debug decoder sidecars (eukhe-*.debug / *.debug.gz) are release
# assets for offline symbolication, NEVER install payload: consumers (the
# Nix flake's package.nix) extract the tarball verbatim, so a decoder inside
# it would ship DWARF bytes to every install. eukhe-release.yml uploads the
# decoder as a separate release asset; this assembly hard-fails if one
# appears in the staging tree or the packed archive (guards the future, not
# just today: a later staging mistake must fail the release step, not ride
# the tarball).
DECODER_SUFFIXES = (".debug", ".debug.gz")


def decoder_like(path: Path) -> bool:
    return path.name.endswith(DECODER_SUFFIXES)


def fail_if_decoder_in_tree(staging: Path) -> None:
    offenders = sorted(
        str(p.relative_to(staging))
        for p in staging.rglob("*") if p.is_file() and decoder_like(p)
    )
    if offenders:
        fail(
            "decoder-like sidecar(s) in the release payload (split-debug "
            "assets are separate release assets, never install payload): "
            + ", ".join(offenders)
        )


def fail_if_decoder_in_archive(archive_path: Path) -> None:
    with tarfile.open(archive_path, "r:gz") as archive:
        offenders = sorted(
            m.name for m in archive.getmembers()
            if decoder_like(Path(m.name))
        )
    if offenders:
        archive_path.unlink(missing_ok=True)
        fail(
            f"decoder-like sidecar(s) packed into {archive_path.name} "
            "(split-debug assets are separate release assets, never install "
            f"payload): {', '.join(offenders)}"
        )


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--version", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--binary", type=Path, default=None)
    parser.add_argument("--decoder", type=Path, default=None,
                        help="separate Linux .debug.gz sidecar from split_debug.py")
    parser.add_argument("--runtime-dir", type=Path, default=None)
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument("--catalog-assets", type=Path, default=None,
                        help="directory with models.bundled.json + "
                             "mcp-services.bundled.json (see "
                             "scripts/release/bundle_catalog.py)")
    return parser.parse_args()


def resolve_binary(args: argparse.Namespace) -> Path:
    candidates = []
    if args.binary is not None:
        candidates.append(args.binary)
    else:
        candidates.append(args.repo_root / "target" / args.target / "release" / BINARY_NAME)
        candidates.append(args.repo_root / "target" / "release" / BINARY_NAME)
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    listed = ", ".join(str(candidate) for candidate in candidates)
    fail(f"no executable {BINARY_NAME} binary found (looked at: {listed}); build first")


def validate_version(version: str) -> None:
    if not VERSION_RE.match(version):
        fail(f"invalid version {version!r} (expected semver like 0.1.0)")


def copy_runtime_tree(source: Path, target: Path) -> None:
    """Copy the kernel sidecar, dropping the dev-only files
    (RUNTIME_EXCLUDED_*): a plain-file, no-link tree like the rest of the
    payload (symlinks still fail at pack time in `_deterministic_member`).
    """

    def ignore(directory, names):
        return {
            name for name in names
            if name in RUNTIME_EXCLUDED_NAMES
            or name.endswith(RUNTIME_EXCLUDED_SUFFIXES)
        }

    shutil.copytree(source, target, ignore=ignore)


def stage_tree(staging: Path, args: argparse.Namespace) -> dict:
    """Copy the tarball payload into the staging dir; return per-entry facts.

    The runtime entry ships the curated content (see
    RUNTIME_EXCLUDED_*); every other entry is a
    verbatim copy.
    """
    binary = resolve_binary(args)
    runtime_dir = args.runtime_dir or (args.repo_root / "eukhe-runtime")
    sources = {
        BINARY_NAME: binary,
        "eukhe-runtime": runtime_dir,
        "skills": args.repo_root / "skills",
        "LICENSE": args.repo_root / "LICENSE",
        "README.md": args.repo_root / "README.md",
    }
    if not runtime_dir.joinpath("pyproject.toml").is_file():
        fail(
            "kernel runtime sidecar not found at "
            f"{runtime_dir} (expected eukhe-runtime with pyproject.toml); "
            "pass --runtime-dir or merge the kernel-packaging lane"
        )
    # The bootstrap installs nothing that is not an exact, hashed pin.
    try:
        read_runtime_lock(runtime_dir)
    except LockError as error:
        fail(f"kernel runtime lock rejected: {error}")
    for name, source in sources.items():
        target_path = staging / name
        if not source.exists():
            fail(f"release payload entry {name!r} missing at {source}")
        if source.is_dir():
            if name == "eukhe-runtime":
                copy_runtime_tree(source, target_path)
            elif name == "skills":
                shutil.copytree(source, target_path, ignore=lambda _directory, names: {
                    entry for entry in names
                    if entry in RUNTIME_EXCLUDED_NAMES
                    or entry.endswith(RUNTIME_EXCLUDED_SUFFIXES)
                })
            else:
                shutil.copytree(source, target_path)
        else:
            shutil.copy2(source, target_path)
    # Executable for the `--version` probes (the tar member filter re-pins
    # the mode in the archive).
    os.chmod(staging / BINARY_NAME, 0o755)
    # The bundled catalog assets gate (spec §3.9): the release packer FAILS
    # without validated assets — generate them first (the live catalog repo
    # the release workflow uses, or a local catalog checkout) via
    # scripts/release/bundle_catalog.py.
    if args.catalog_assets is None:
        fail(
            "missing bundled catalog assets: run "
            "`python3 scripts/release/bundle_catalog.py generate "
            "--catalog-dir <prime-agent-catalog>` (live repo: --network) "
            "and pass "
            "--catalog-assets <dir>"
        )
    catalog_assets = Path(args.catalog_assets)
    catalog_facts = validate_bundled_catalog_dir(catalog_assets)
    for name in BUNDLED_CATALOG_FILES:
        shutil.copyfile(catalog_assets / name, staging / name)
    payload = list(STAGED_ENTRIES)
    # The payload guard runs on the staged tree BEFORE packing: a decoder
    # sidecar staged by a later change fails here, not in the field.
    fail_if_decoder_in_tree(staging)
    return {
        "executable_sha256": sha256_file(staging / BINARY_NAME),
        "payload": payload,
        "catalog_assets": catalog_facts,
    }


def _deterministic_member(member: tarfile.TarInfo) -> tarfile.TarInfo:
    """tarfile `filter`: fixed mtime/owner, deterministic modes, no links.

    Equivalent to GNU tar's `--sort=name --owner=0 --group=0 --numeric-owner
    --mtime=@0`; the binary keeps its exec bit, everything else is 0644/0755.
    """
    if member.issym() or member.islnk():
        raise ValueError(
            f"tarball payload contains a link entry {member.name!r}; "
            "the release payload must be plain files and directories"
        )
    member.uid = 0
    member.gid = 0
    member.uname = "root"
    member.gname = "root"
    member.mtime = 0
    if member.isdir():
        member.mode = 0o755
    elif member.name == BINARY_NAME:
        member.mode = 0o755
    else:
        member.mode = 0o644
    return member


def pack_tarball(staging: Path, out_path: Path, entries: list[str]) -> None:
    """Deterministic tar.gz with files at the tarball root.

    bsdtar vs GNU tar quirks are avoided by writing the archive through
    Python's tarfile with explicit member metadata.
    """
    staging_abs = staging.resolve()
    try:
        # Gzip mtime is pinned so two assemblies of identical input produce
        # byte-identical archives (the tar member metadata is pinned below).
        with open(out_path, "wb") as raw, \
             gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz, \
             tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for name in sorted(entries):
                path = staging_abs / name
                if path.is_dir():
                    archive.add(path, arcname=name, recursive=True,
                                filter=_deterministic_member)
                else:
                    archive.add(path, arcname=name, recursive=False,
                                filter=_deterministic_member)
    except ValueError as error:
        out_path.unlink(missing_ok=True)
        fail(str(error))


def debug_sections(binary: Path) -> list[str]:
    """ELF .debug_* section names, so the split asserts on real evidence."""
    result = subprocess.run(["objdump", "-h", str(binary)], capture_output=True, text=True)
    if result.returncode != 0:
        fail(f"objdump -h failed on {binary}: {result.stderr.strip()}")
    return [
        line.split()[1]
        for line in result.stdout.splitlines()
        if line[:1].isspace() and ".debug" in line
    ]


def gnu_build_id(path: Path) -> str:
    result = subprocess.run(["readelf", "-n", str(path)],
                            capture_output=True, text=True)
    match = re.search(r"Build ID: ([0-9a-f]+)", result.stdout) if result.returncode == 0 else None
    if match is None:
        fail(f"no GNU build ID in {path}: {result.stderr.strip()}")
    return match.group(1)


def decoder_facts(args: argparse.Namespace) -> dict | None:
    if args.target.endswith("-unknown-linux-gnu"):
        if args.binary is None or args.decoder is None:
            fail("Linux release requires explicit --binary shipped ELF and "
                 "--decoder from split_debug.py")
        if debug_sections(resolve_binary(args)):
            fail(f"Linux shipped ELF still has DWARF: {args.binary}")
        expected = f"eukhe-{args.version}-{TARGET_ALIASES[args.target]}.debug.gz"
        decoder = args.decoder
        if decoder.name != expected or not decoder.is_file():
            fail(f"missing required Linux decoder {expected}")
        binary = resolve_binary(args)
        with tempfile.TemporaryDirectory(prefix="eukhe-decoder-") as tmp:
            uncompressed = Path(tmp) / "eukhe.debug"
            try:
                with gzip.open(decoder, "rb") as src, uncompressed.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
            except (OSError, EOFError) as error:
                fail(f"cannot decompress decoder {decoder}: {error}")
            build_id = gnu_build_id(binary)
            if gnu_build_id(uncompressed) != build_id:
                fail(f"decoder build ID does not match shipped ELF {binary}")
        return {"target": args.target, "file": expected,
                "sha256": sha256_file(decoder), "buildId": build_id,
                "executableSha256": sha256_file(binary)}
    if args.decoder is not None:
        fail("decoder is only supported for Linux targets")
    return None


def main() -> int:
    args = parse_args()
    validate_version(args.version)
    if args.target not in TARGET_ALIASES:
        fail(f"unknown release target {args.target!r} (known: {', '.join(TARGET_ALIASES)})")

    decoder = decoder_facts(args)
    out_dir = (args.out_dir or args.repo_root / "target" / "release" / "dist").resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix="eukhe-archive-"))
    try:
        facts = stage_tree(staging, args)
        archive_name = (
            f"eukhe-{args.version}-{TARGET_ALIASES[args.target]}.tar.gz"
        )
        archive_path = out_dir / archive_name
        pack_tarball(staging, archive_path, facts["payload"])
        # The packed archive is the published artifact: assert it carries
        # no decoder sidecar before anything records its hash.
        fail_if_decoder_in_archive(archive_path)
        archive_sha256 = sha256_file(archive_path)
    finally:
        shutil.rmtree(staging, ignore_errors=True)

    # The validated asset counts (models / transport tuples / services) ride
    # the build log, not the manifest entry.
    print(f"bundled catalog assets: {json.dumps(facts['catalog_assets'])}")

    entry = {
        "version": f"v{args.version}",
        "platform": TARGET_ALIASES[args.target],
        "target": args.target,
        "file": archive_name,
        "sha256": archive_sha256,
        "executableSha256": facts["executable_sha256"],
    }

    # Merge-or-write semantics: several per-target runs into one out-dir
    # combine their entries (eukhe-release.yml's publish job reads each
    # build job's manifest.json).
    manifest_path = out_dir / "manifest.json"
    manifest = {"version": f"v{args.version}", "binaries": []}
    if manifest_path.exists():
        existing = json.loads(manifest_path.read_text())
        if existing.get("version") == manifest["version"]:
            manifest["binaries"] = existing["binaries"]
            previous = existing.get("decoders", [])
            targets = [d["target"] for d in previous]
            if len(targets) != len(set(targets)):
                fail("existing manifest has duplicate decoder target entries")
            if previous:
                manifest["decoders"] = previous
    manifest["binaries"] = [
        b for b in manifest["binaries"] if b.get("target") != args.target
    ] + [entry]
    manifest["binaries"].sort(key=lambda b: b["file"])
    decoders = [d for d in manifest.get("decoders", [])
                if d.get("target") != args.target]
    if decoder is not None:
        decoders.append(decoder)
    if decoders:
        manifest["decoders"] = sorted(decoders, key=lambda d: d["file"])
    else:
        manifest.pop("decoders", None)
    sums_path = out_dir / "SHA256SUMS"
    artifacts = manifest["binaries"] + manifest.get("decoders", [])
    files = [artifact["file"] for artifact in artifacts]
    if len(files) != len(set(files)):
        fail("manifest contains duplicate artifact filenames")
    lines = [f"{artifact['sha256']}  {artifact['file']}"
             for artifact in sorted(artifacts, key=lambda item: item["file"])]
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    sums_path.write_text("\n".join(lines) + "\n")

    print(json.dumps(entry, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
