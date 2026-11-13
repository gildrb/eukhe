#!/usr/bin/env bash
# Print the path of the bend skill (its bend/ folder) at the commit
# BEND_SKILL_REV that scripts/toolchain.env pins: a clone of
# github.com/gildrb/skills in ~/.cache/eukhe/bend-skill/<rev>, made once.
# The lock gate runs this gate.py (scripts/ci_local.sh laws_lock and relock,
# site/scripts/laws.sh): its verdict on LAWS.lock depends on the gate's code,
# so the gate is pinned like Bend. Exits 1, naming the commit, when the clone
# fails, or the cache holds another commit or changed files.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=scripts/toolchain.env
source scripts/toolchain.env

dir="${HOME}/.cache/eukhe/bend-skill/${BEND_SKILL_REV}"
if [[ ! -d "${dir}" ]]; then
  mkdir -p "$(dirname "${dir}")"
  tmp="$(mktemp -d "${dir}.XXXXXX")"
  trap 'rm -rf "${tmp}"' EXIT
  git clone --quiet --no-checkout https://github.com/gildrb/skills "${tmp}" >&2 || {
    echo "the bend skill at ${BEND_SKILL_REV} (scripts/toolchain.env BEND_SKILL_REV) could not be cloned from https://github.com/gildrb/skills" >&2
    exit 1
  }
  git -C "${tmp}" -c advice.detachedHead=false checkout --quiet "${BEND_SKILL_REV}" >&2
  [[ -d "${dir}" ]] || mv "${tmp}" "${dir}"
fi
have="$(git -C "${dir}" rev-parse HEAD 2>/dev/null || true)"
if [[ "${have}" != "${BEND_SKILL_REV}" ]] || [[ -n "$(git -C "${dir}" status --porcelain --untracked-files=no)" ]]; then
  echo "${dir} is not the bend skill at ${BEND_SKILL_REV} (scripts/toolchain.env BEND_SKILL_REV): it holds ${have:-no commit} or changed files. Remove it and run again." >&2
  exit 1
fi
echo "${dir}/bend"
