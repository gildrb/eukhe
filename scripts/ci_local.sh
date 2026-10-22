#!/usr/bin/env bash
# The CI gates of eukhe (docs/develop.md). They run only here: GitHub runs
# no gate. prek runs them as git hooks (.pre-commit-config.yaml; `make
# hooks` installs them).
#
#   scripts/ci_local.sh fast      `make ci-fast`, the pre-commit gate:
#                                 rustfmt, the secrets scan of the staged
#                                 diff, and clippy on the crates the staged
#                                 change touches.
#   scripts/ci_local.sh full      `make ci-local`: the full gate, on the
#                                 current tree.
#   scripts/ci_local.sh pre-push  the pre-push gate: `make ci-local` on the
#                                 pushed commit (PRE_COMMIT_TO_REF, from
#                                 prek) in a separate worktree of it
#                                 (<repo>-ci beside the main checkout: a
#                                 path under .git hides the tests from
#                                 vitest and makes test socket paths too
#                                 long), so uncommitted and untracked files
#                                 do not change the result. The worktree
#                                 keeps its own target/ between pushes. All
#                                 worktrees share it: one push at a time runs the
#                                 gate (flock on eukhe-ci-local.lock), the
#                                 others wait. A commit that passed once
#                                 (eukhe-ci-local-passed/<sha>) pushes
#                                 again without the gate.
#
# Each gate prints its name; a failed gate prints `ci-<mode>: gate <name>
# FAILED` and the script stops with its exit code. The full gate runs the
# Rust lane (check, clippy, tests) and the other lane (secrets, deny, laws,
# runtime tests, dashboard UI) at the same time; the second lane's log
# prints when it ends.
#
# CI_LOCAL_SECRETS_RANGE: the `git log` range the full gate scans for
# secrets (pre-push gives the pushed commits). Default: origin/main..HEAD.
set -euo pipefail
unset RUSTUP_TOOLCHAIN
cd "$(dirname "$0")/.."
mode="${1:?usage: scripts/ci_local.sh fast|full|pre-push}"
export BEND_NO_TELEMETRY=1
# BEND_VERSION and LEAN_VERSION.
# shellcheck source=scripts/toolchain.env
source scripts/toolchain.env

gate() {
  local name="$1" rc
  shift
  echo "==> ci-${mode}: ${name}"
  set +e
  (set -e; "$@")
  rc=$?
  set -e
  if [[ ${rc} -ne 0 ]]; then
    echo "ci-${mode}: gate '${name}' FAILED (exit ${rc})" >&2
    exit "${rc}"
  fi
}

check_bend() {
  local have
  command -v bend >/dev/null 2>&1 || {
    echo "bend is not installed. Install Bend ${BEND_VERSION}, the release that scripts/toolchain.env pins."
    return 1
  }
  have="$(bend version | awk '{ print $2 }')"
  [[ "${have}" == "${BEND_VERSION}" ]] || {
    echo "bend ${have} is installed, but scripts/toolchain.env pins Bend ${BEND_VERSION}. Install Bend ${BEND_VERSION}."
    return 1
  }
}

check_lean() {
  local have
  command -v lean >/dev/null 2>&1 || {
    echo "lean is not installed. bend --verdict needs Lean ${LEAN_VERSION}, the release that scripts/toolchain.env pins."
    return 1
  }
  have="$(lean --version | sed -n 's/^Lean (version \([0-9.]*\),.*/\1/p')"
  [[ "${have}" == "${LEAN_VERSION}" ]] || {
    echo "lean ${have} is installed, but scripts/toolchain.env pins Lean ${LEAN_VERSION}. Install Lean ${LEAN_VERSION}."
    return 1
  }
}

check_tools() {
  local tool missing=()
  for tool in "$@"; do
    command -v "${tool}" >/dev/null 2>&1 || missing+=("${tool}")
  done
  [[ ${#missing[@]} -eq 0 ]] || { echo "not installed: ${missing[*]} (nix develop has them)"; return 1; }
}

# The staged change as ci_pr_crates.py rows: `<path>` TAB `<old path>`.
staged_rows() {
  git diff --cached --name-status -M --no-color | awk -F'\t' '
    $1 ~ /^[RC]/ { print $3 "\t" $2; next }
    { print $2 "\t" }'
}

# A docs-only change (the hooks skip rule): every path is a Markdown file
# in docs/ or at the repository root. Crates embed their own Markdown, so
# Markdown elsewhere counts as code.
docs_only() {
  local path any=0
  while IFS= read -r path; do
    [[ -z "${path}" ]] && continue
    any=1
    [[ "${path}" == *.md && ( "${path}" != */* || "${path}" == docs/* ) ]] || return 1
  done
  [[ ${any} -eq 1 ]]
}

clippy_touched() {
  local rows out crates args=()
  rows="$(staged_rows)"
  if [[ -z "${rows}" ]]; then
    echo "nothing staged: clippy skipped"
    return 0
  fi
  if cut -f1,2 <<<"${rows}" | tr '\t' '\n' | docs_only; then
    echo "docs-only change (Markdown in docs/ or at the root): clippy skipped"
    return 0
  fi
  out="$(mktemp)"
  GITHUB_OUTPUT="${out}" python3 scripts/ci_pr_crates.py <<<"${rows}"
  crates="$(sed -n 's/^crates=//p' "${out}")"
  rm -f "${out}"
  if [[ -z "${crates}" ]]; then
    cargo clippy --workspace --all-targets --locked -- -D warnings
  else
    for crate in ${crates//,/ }; do args+=(-p "${crate}"); done
    cargo clippy "${args[@]}" --all-targets --locked -- -D warnings
  fi
}

secrets_staged() {
  if ! command -v gitleaks >/dev/null 2>&1; then
    echo "gitleaks is not installed: the staged diff is not scanned (the pre-push gate scans the pushed commits)"
    return 0
  fi
  gitleaks git --pre-commit --staged --redact --no-banner --config .gitleaks.toml .
}

secrets_range() {
  local range="${CI_LOCAL_SECRETS_RANGE:-origin/main..HEAD}"
  check_tools gitleaks
  echo "scanning: ${range}"
  gitleaks git --redact --no-banner --config .gitleaks.toml --log-opts="${range}" .
}

laws() {
  local out
  out="$(mktemp -d)"
  python3 scripts/check_laws_wired.py .
  bend PROOF.bend | tee "${out}/proof.out"
  grep -qx 'ALL PROOFS CHECK' "${out}/proof.out"
  EUKHE_REQUIRE_BEND=1 python3 scripts/release/test_next_version.py
  bend PROOF.bend --verdict | tee "${out}/verdict.out"
  grep -qx 'ALL PROOFS CHECK' "${out}/verdict.out"
  rm -rf "${out}"
}

dashboard_ui() {
  EUKHE_REQUIRE_BEND=1 make --no-print-directory dashboard-ui
  git diff --exit-code --stat -- crates/eukhe-dashboard/web
  test -z "$(git status --porcelain -- crates/eukhe-dashboard/web)"
}

# `cargo test --workspace`, split: the test units go to TEST_SHARDS shards
# (scripts/ci_test_shard.py, a stable assignment), all shards run at the
# same time on one build, then scripts/ci_test_shard_summary.py audits that
# the shards ran every unit exactly once. The environment is the clean one
# of AGENTS.md: inherited EUKHE_* variables would point test daemons at
# real state.
TEST_SHARDS=8

clean_env() {
  env -i HOME="${HOME}" PATH="${PATH}" USER="${USER:-}" LANG="${LANG:-C.UTF-8}" \
    EUKHE_REQUIRE_BEND=1 BEND_NO_TELEMETRY=1 "$@"
}

workspace_tests() {
  local total="${TEST_SHARDS}" dir shard pids=() failed=0
  dir="$(mktemp -d)"
  clean_env cargo test --workspace --locked --no-run
  clean_env cargo build --workspace --bins --locked
  echo "running ${total} test shards at the same time (logs: ${dir})"
  for shard in $(seq 1 "${total}"); do
    (trap - INT; clean_env python3 scripts/ci_test_shard.py --shard "${shard}" --total "${total}" \
      --manifest "${dir}/shard-manifest-${shard}.json") </dev/null >"${dir}/shard-${shard}.log" 2>&1 &
    pids+=("$!")
  done
  for shard in $(seq 1 "${total}"); do
    if ! wait "${pids[shard - 1]}"; then
      failed=1
      echo "==> test shard ${shard}/${total} failed; its log:"
      cat "${dir}/shard-${shard}.log"
    fi
  done
  python3 scripts/ci_test_shard_summary.py --total "${total}" --dir "${dir}"
  [[ ${failed} -eq 0 ]]
  rm -rf "${dir}"
}

side_lane() {
  gate secrets secrets_range
  gate deny make --no-print-directory deny
  gate laws laws
  gate runtime-test make --no-print-directory runtime-test
  gate dashboard-ui dashboard_ui
}

case "${mode}" in
  fast)
    gate "bend version" check_bend
    gate fmt cargo fmt --all --check
    gate secrets secrets_staged
    gate "clippy (touched crates)" clippy_touched
    ;;
  full)
    start=${SECONDS}
    gate tools check_tools cargo uv npm python3 cargo-deny
    gate "bend version" check_bend
    gate "lean version" check_lean
    gate fmt cargo fmt --all --check
    # The other lane runs in the background. Bash starts a background job
    # with SIGINT ignored, and the eukhe-runtime tests send SIGINT, so the
    # job restores the default action first (`trap - INT`); Ctrl+C then
    # stops every lane. The Rust lane runs in the foreground: its pty tests
    # need the terminal state of a foreground job.
    log="$(mktemp)"
    (trap - INT; side_lane) </dev/null >"${log}" 2>&1 &
    side=$!
    set +e
    (
      set -e
      gate check cargo check --workspace --all-targets --locked
      gate clippy cargo clippy --workspace --all-targets --locked -- -D warnings
      gate test workspace_tests
    )
    rust_rc=$?
    wait "${side}"
    side_rc=$?
    set -e
    echo "==> ci-full: secrets, deny, laws, runtime-test, dashboard-ui log"
    cat "${log}"
    rm -f "${log}"
    echo "ci-full: $((SECONDS - start))s"
    if [[ ${rust_rc} -ne 0 || ${side_rc} -ne 0 ]]; then
      echo "ci-full: FAILED (the failed gates are named above)" >&2
      exit 1
    fi
    echo "ci-full: every gate passed"
    ;;
  pre-push)
    to="${PRE_COMMIT_TO_REF:?PRE_COMMIT_TO_REF is unset: prek gives it in the pre-push hook}"
    from="${PRE_COMMIT_FROM_REF:-}"
    common="$(cd "$(git rev-parse --git-common-dir)" && pwd)"
    worktree="$(dirname "${common}")-ci"
    passed="${common}/eukhe-ci-local-passed"
    if [[ -e "${passed}/${to}" ]]; then
      echo "pre-push: ${to:0:12} passed make ci-local before"
      exit 0
    fi
    command -v flock >/dev/null 2>&1 || { echo "pre-push: flock not installed (util-linux; macOS: brew install flock)" >&2; exit 1; }
    exec 9>"${common}/eukhe-ci-local.lock"
    if ! flock -n 9; then
      echo "pre-push: another push runs make ci-local; waiting for it"
      flock 9
    fi
    if [[ -e "${passed}/${to}" ]]; then
      echo "pre-push: ${to:0:12} passed make ci-local before"
      exit 0
    fi
    unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
    if [[ -n "${from}" && ! "${from}" =~ ^0+$ ]] && git cat-file -e "${from}^{commit}" 2>/dev/null; then
      range="${from}..${to}"
    else
      range="${to} --not --remotes=${PRE_COMMIT_REMOTE_NAME:-origin}"
    fi
    if [[ -e "${worktree}/.git" ]]; then
      git -C "${worktree}" checkout --quiet --detach --force "${to}"
      git -C "${worktree}" clean --quiet -fdx -e /target/ -e node_modules/
    else
      git worktree prune
      git worktree add --quiet --detach --force "${worktree}" "${to}"
    fi
    echo "pre-push: make ci-local on ${to:0:12} in ${worktree}"
    # 9>&-: a process the gate leaves behind never holds the lock.
    if ! CI_LOCAL_SECRETS_RANGE="${range}" make --no-print-directory -C "${worktree}" ci-local 9>&-; then
      echo "pre-push: a gate failed on ${to:0:12} (its name is above). The push stops. Fix the cause, commit, and push again." >&2
      exit 1
    fi
    mkdir -p "${passed}"
    : >"${passed}/${to}"
    ;;
  *)
    echo "usage: scripts/ci_local.sh fast|full|pre-push" >&2
    exit 2
    ;;
esac
