#!/usr/bin/env bash
# Print the path of the Bend executable at the BEND_VERSION that
# scripts/toolchain.env pins (the single pin): mise's install of that exact
# version when mise has one, else the first `bend` on PATH whose
# `bend version` is it. A version manager's global default (or its shims)
# may be another release; the gates run this one. Exits 1, naming the
# missing version, when none is installed.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=scripts/toolchain.env
source scripts/toolchain.env

is_pinned() {
  [[ -x "$1" ]] && [[ "$("$1" version 2>/dev/null)" == "bend ${BEND_VERSION}" ]]
}

if command -v mise >/dev/null 2>&1; then
  dir="$(mise where "github:bendlang/bend@${BEND_VERSION}" 2>/dev/null || true)"
  if [[ -n "${dir}" ]] && is_pinned "${dir}/bin/bend"; then
    echo "${dir}/bin/bend"
    exit 0
  fi
fi
while IFS= read -r candidate; do
  if is_pinned "${candidate}"; then
    echo "${candidate}"
    exit 0
  fi
done < <(type -ap bend)
echo "Bend ${BEND_VERSION} (scripts/toolchain.env) is not installed: install it (mise install github:bendlang/bend@${BEND_VERSION}, or https://bend-lang.com/install.sh) and keep it on PATH or in mise." >&2
exit 1
