#!/usr/bin/env python3
"""Write the `.tar.xz` twin of each release `.tar.gz`: the same tar bytes.

The release publishes both archives of every platform. install.sh (when the
machine can unpack it) and `eukhe update` download the `.tar.xz`, about a
third smaller; the `.tar.gz` stays for the Nix flake, machines without xz and
the updaters of releases before the twins. The tar inside is byte-identical:
the twin is decompressed again and compared before it is kept.

xz runs single-threaded (`-T1`, so the bytes do not depend on the runner's
core count) at preset 9e, after the branch-call filter of the platform's
machine code: x86 on linux-x64 (every xz decodes it), ARM64 on the arm64
platforms (xz >= 5.4 decodes it; install.sh falls back to the `.tar.gz` on
an older one). Encoding needs xz >= 5.4 here.

Usage:
    python3 scripts/release/xz_archives.py <eukhe-<version>-<platform>.tar.gz>...

Prints `<sha256>  <name>` of each twin, in SHA256SUMS form.
"""

from __future__ import annotations

import gzip
import hashlib
import re
import subprocess
import sys
from pathlib import Path

# The branch-call filter per platform alias (assemble_artifacts.TARGET_ALIASES).
FILTERS = {
    "linux-x64": "--x86",
    "linux-arm64": "--arm64",
    "darwin-arm64": "--arm64",
}
ARCHIVE = re.compile(r"^eukhe-\d+\.\d+\.\d+-(?P<alias>[a-z0-9-]+)\.tar\.gz$")


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


def check_xz() -> None:
    try:
        out = subprocess.run(["xz", "--version"], capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"xz is required: {error}")
    match = re.search(r"xz \(XZ Utils\) (\d+)\.(\d+)", out)
    if match is None or (int(match[1]), int(match[2])) < (5, 4):
        fail(f"xz >= 5.4 is required (the ARM64 filter): {out.splitlines()[0] if out else out!r}")


def twin(gz: Path) -> Path:
    """Writes `<name>.tar.xz` beside `gz`; returns its path."""
    match = ARCHIVE.match(gz.name)
    if match is None or match["alias"] not in FILTERS:
        fail(f"{gz.name} is not a release archive eukhe-<version>-<platform>.tar.gz")
    tar = gzip.decompress(gz.read_bytes())
    command = ["xz", "-T1", "--format=xz", "--check=crc64", FILTERS[match["alias"]],
               "--lzma2=preset=9e", "--stdout"]
    packed = subprocess.run(command, input=tar, capture_output=True, check=False)
    if packed.returncode != 0:
        fail(f"{' '.join(command)} failed on {gz.name}: {packed.stderr.decode().strip()}")
    back = subprocess.run(["xz", "-d", "--stdout"], input=packed.stdout,
                          capture_output=True, check=False)
    if back.returncode != 0 or back.stdout != tar:
        fail(f"the .tar.xz of {gz.name} does not decompress to its tar")
    out = gz.with_name(gz.name.removesuffix(".gz") + ".xz")
    out.write_bytes(packed.stdout)
    return out


def main() -> int:
    if len(sys.argv) < 2:
        fail("usage: xz_archives.py <archive.tar.gz>...")
    check_xz()
    for name in sys.argv[1:]:
        out = twin(Path(name))
        print(f"{hashlib.sha256(out.read_bytes()).hexdigest()}  {out.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
