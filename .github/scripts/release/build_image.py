#!/usr/bin/env python3
"""The release toolchain image (.github/scripts/release/Dockerfile), run by
.github/workflows/build-image.yml: one `push` per architecture on a native
runner, then `merge`.

  build_image.py build <tag>  build ${IMAGE}:<tag>-<arch> for this machine's
                              architecture and print the installed packages
  build_image.py push <tag>   build, then push ${IMAGE}:<tag>-<arch>
  build_image.py merge <tag>  ${IMAGE}:<tag> = the amd64 + arm64 images;
                              prints the multi-arch digest to pin

The image records the archive it was built from and the packages it
installed, with their versions, in /usr/share/eukhe-build and in its labels
org.gildrb.eukhe-build.{apt-source,packages}.
<tag> is jammy-<YYYYMMDD>; IMAGE defaults to ghcr.io/gildrb/eukhe-build.
push and merge need `docker login ghcr.io` first.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

DOCKERFILE = Path(__file__).resolve().parent / "Dockerfile"


def docker(*args: str, stdin: bytes | None = None) -> str:
    """docker's stdout without its trailing newlines; raises when docker fails."""
    return subprocess.run(
        ["docker", *args], input=stdin, stdout=subprocess.PIPE, check=True
    ).stdout.decode().rstrip("\n")


def build(image: str, tag: str) -> str:
    """Build and label ${IMAGE}:<tag>-<arch>; its reference."""
    arch = docker("version", "--format", "{{.Server.Arch}}")
    if arch not in ("amd64", "arm64"):
        print(f"unsupported architecture {arch}", file=sys.stderr)
        raise SystemExit(1)
    ref = f"{image}:{tag}-{arch}"
    # No cache and a fresh base: the image holds exactly what the Dockerfile
    # installs today. No provenance/SBOM manifests: a plain image per arch.
    subprocess.run(
        ["docker", "buildx", "build", "--pull", "--no-cache", "--provenance=false", "--sbom=false",
         "--platform", f"linux/{arch}", "--load", "-t", ref, "-"],
        input=DOCKERFILE.read_bytes(),
        check=True,
    )
    source = docker("run", "--rm", ref, "cat", "/usr/share/eukhe-build/source")
    packages = docker("run", "--rm", ref, "cat", "/usr/share/eukhe-build/packages.txt")
    print(f"{ref}: apt source {source}")
    print(f"{ref}: installed packages")
    print(packages, flush=True)
    # The same image, with the apt source and the installed packages as labels.
    subprocess.run(
        ["docker", "buildx", "build", "--provenance=false", "--sbom=false",
         "--platform", f"linux/{arch}", "--load", "-t", ref,
         "--label", f"org.gildrb.eukhe-build.apt-source={source}",
         "--label", f"org.gildrb.eukhe-build.packages={packages.replace(chr(10), ' ')}", "-"],
        input=f"FROM {ref}\n".encode(),
        check=True,
    )
    return ref


def merge(image: str, tag: str) -> None:
    subprocess.run(
        ["docker", "buildx", "imagetools", "create", "-t", f"{image}:{tag}", f"{image}:{tag}-amd64", f"{image}:{tag}-arm64"],
        check=True,
    )
    digest = ""
    for line in docker("buildx", "imagetools", "inspect", f"{image}:{tag}").splitlines():
        fields = line.split()
        if fields and fields[0] == "Digest:":
            digest = fields[1] if len(fields) > 1 else ""
            break
    if not digest.startswith("sha256:"):
        print(f"no digest for {image}:{tag}", file=sys.stderr)
        raise SystemExit(1)
    print(f"pin: {image}:{tag}@{digest}")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write(f"pin: `{image}:{tag}@{digest}`\n")


def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] not in ("build", "push", "merge") or not re.fullmatch(r"jammy-[0-9]{8}", sys.argv[2]):
        print(f"usage: {sys.argv[0]} build|push|merge jammy-<YYYYMMDD>", file=sys.stderr)
        return 2
    mode, tag = sys.argv[1], sys.argv[2]
    image = os.environ.get("IMAGE") or "ghcr.io/gildrb/eukhe-build"
    sys.stdout.reconfigure(line_buffering=True)
    try:
        if mode == "merge":
            merge(image, tag)
        else:
            ref = build(image, tag)
            if mode == "push":
                subprocess.run(["docker", "push", ref], check=True)
    except subprocess.CalledProcessError as failed:
        return failed.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
