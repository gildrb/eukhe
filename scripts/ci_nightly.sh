#!/usr/bin/env bash
# The nightly gate and release of eukhe. A systemd user
# timer runs it once a night.
#
#   scripts/ci_nightly.sh run     the full gate (`make ci-local`) on
#                                 origin/main, in the gate worktree
#                                 (<repo>-ci beside the main checkout: a path
#                                 under .git hides the tests from vitest and
#                                 makes test socket paths too long). When it
#                                 passes, it starts the release of that
#                                 commit (`gh workflow run eukhe-release.yml
#                                 -f sha=<commit>`). When it fails, nothing
#                                 is released.
#   scripts/ci_nightly.sh status  the result of the last run.
#
# Each run appends its result to ~/.eukhe/ci/nightly.log: one line with the
# time, the commit and the result, and for a failure the failed gates and
# test units. The full output of the last run is ~/.eukhe/ci/nightly-last.log.
# A commit that already has an eukhe-v* tag is not run again. One run at a
# time (flock on <git common dir>/eukhe-ci-nightly.lock).
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:?usage: scripts/ci_nightly.sh run|status}"
state="${HOME}/.eukhe/ci"
summary="${state}/nightly.log"
last="${state}/nightly-last.log"

case "${mode}" in
  status)
    if [[ ! -s "${summary}" ]]; then
      echo "no nightly run yet (${summary} is empty)"
      exit 0
    fi
    # The last record: its result line and the detail lines under it.
    awk '/^[0-9]{4}-[0-9]{2}-[0-9]{2}T/ { record = "" } { record = record $0 "\n" } END { printf "%s", record }' "${summary}"
    ;;
  run)
    command -v flock >/dev/null 2>&1 || { echo "flock not installed (util-linux)" >&2; exit 1; }
    command -v gh >/dev/null 2>&1 || { echo "gh not installed: the release cannot start" >&2; exit 1; }
    mkdir -p "${state}"
    common="$(cd "$(git rev-parse --git-common-dir)" && pwd)"
    worktree="$(dirname "${common}")-ci"
    exec 9>"${common}/eukhe-ci-nightly.lock"
    flock -n 9 || { echo "another nightly run is in progress" >&2; exit 1; }
    git fetch --quiet --tags origin
    sha="$(git rev-parse origin/main)"
    stamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    released="$(git tag --points-at "${sha}" --list 'eukhe-v*')"
    if [[ -n "${released}" ]]; then
      echo "${stamp} ${sha:0:12} skipped: already released as ${released//$'\n'/, }" | tee -a "${summary}"
      exit 0
    fi
    previous="$(git describe --tags --abbrev=0 --match 'eukhe-v*' "${sha}" 2>/dev/null || true)"
    if [[ -e "${worktree}/.git" ]]; then
      git -C "${worktree}" checkout --quiet --detach --force "${sha}"
      git -C "${worktree}" clean --quiet -fdx -e /target/ -e node_modules/
    else
      git worktree prune
      git worktree add --quiet --detach --force "${worktree}" "${sha}"
    fi
    # Every night builds from an empty build dir: cargo never deletes stale
    # build files, and one day of gate runs grew this dir to 410 GB.
    (cd "${worktree}" && cargo clean --quiet) </dev/null 9>&-
    start=${SECONDS}
    set +e
    # 9>&-: a process the gate leaves behind never holds the lock.
    CI_LOCAL_SECRETS_RANGE="${previous:+${previous}..}${sha}" \
      nice -n 10 make --no-print-directory -C "${worktree}" ci-local </dev/null >"${last}" 2>&1 9>&-
    rc=$?
    set -e
    minutes=$(( (SECONDS - start) / 60 ))
    if [[ ${rc} -ne 0 ]]; then
      {
        echo "${stamp} ${sha:0:12} FAILED after ${minutes} min: no release (full output: ${last})"
        { grep -E "gate '.*' FAILED|FAILED UNITS|^test .* FAILED$" "${last}" || true; } | sed 's/^/  /' | sort -u
      } | tee -a "${summary}"
      exit 1
    fi
    # gh resolves the repo from the git remotes and prefers an `upstream`
    # remote over `origin`, so name the origin repo explicitly.
    repo="$(git remote get-url origin | sed -E 's#.*github\.com[:/]##; s#\.git$##')"
    gh workflow run eukhe-release.yml --repo "${repo}" --ref main -f sha="${sha}"
    echo "${stamp} ${sha:0:12} passed in ${minutes} min: release started" | tee -a "${summary}"
    ;;
  *)
    echo "usage: scripts/ci_nightly.sh run|status" >&2
    exit 2
    ;;
esac
