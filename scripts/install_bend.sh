#!/usr/bin/env bash
# Install the pinned Bend release (2.0.37), checked against its published
# sha256, and put it on the GitHub Actions PATH. With --lean, also install
# the pinned Lean release (4.34.0) that `bend --verdict` builds its BendTT
# kernel with, checked the same way.
#
#   scripts/install_bend.sh [--lean]
#
# Used by CI: the laws job runs `bend PROOF.bend` and `bend PROOF.bend
# --verdict`; the test shards run the Rust-vs-Bend bridge test
# (crates/eukhe-core/src/memory/chat/bridge.rs), which needs `bend` and clang.
set -euo pipefail

BEND_VERSION=2.0.37
# https://github.com/bendlang/bend/releases/tag/v2.0.37 (asset digest)
BEND_SHA256=84c32465a39bc9ac315eade23f470cb8db03153dc860f89564fcfec153c3e445
LEAN_VERSION=4.34.0
# https://github.com/leanprover/lean4/releases/tag/v4.34.0 (asset digest)
LEAN_SHA256=caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b

dir="${RUNNER_TEMP:?RUNNER_TEMP is unset}/bend-toolchain"
mkdir -p "${dir}"

archive="${dir}/bend-${BEND_VERSION}-linux-x64.tar.gz"
curl --proto '=https' --tlsv1.2 -fsSL -o "${archive}" \
  "https://github.com/bendlang/bend/releases/download/v${BEND_VERSION}/bend-${BEND_VERSION}-linux-x64.tar.gz"
echo "${BEND_SHA256}  ${archive}" | sha256sum -c -
tar -xzf "${archive}" -C "${dir}" 2>/dev/null
echo "${dir}/bend/bin" >> "${GITHUB_PATH:?GITHUB_PATH is unset}"

if [ "${1:-}" = "--lean" ]; then
  lean_archive="${dir}/lean-${LEAN_VERSION}-linux.tar.zst"
  curl --proto '=https' --tlsv1.2 -fsSL -o "${lean_archive}" \
    "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst"
  echo "${LEAN_SHA256}  ${lean_archive}" | sha256sum -c -
  tar --zstd -xf "${lean_archive}" -C "${dir}"
  echo "${dir}/lean-${LEAN_VERSION}-linux/bin" >> "${GITHUB_PATH}"
fi
