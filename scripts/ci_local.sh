#!/usr/bin/env bash
# The CI gates of eukhe (docs/develop.md). They run only here: GitHub runs
# no gate. prek runs fast and pre-push as git hooks
# (.pre-commit-config.yaml; `make hooks` installs them); the nightly run
# (scripts/ci_nightly.sh) runs full and releases only when it passes.
#
#   scripts/ci_local.sh fast      `make ci-fast`, the pre-commit gate:
#                                 rustfmt, the secrets scan of the staged
#                                 diff, and clippy on the crates the staged
#                                 change touches.
#   scripts/ci_local.sh pre-push  the pre-push gate, on the pushed commits
#                                 (PRE_COMMIT_FROM_REF..PRE_COMMIT_TO_REF,
#                                 from prek), in this worktree: rustfmt,
#                                 their secrets scan, clippy and `cargo
#                                 test` on the crates they touch, and `bend
#                                 PROOF.bend`. No lock: every worktree
#                                 pushes at any time.
#   scripts/ci_local.sh full      `make ci-local`: the full gate, on the
#                                 current tree.
#
# Each gate prints its name; a failed gate prints `ci-<mode>: gate <name>
# FAILED` and the script stops with its exit code. The full gate runs the
# Rust lane (check, clippy, tests) and the other lane (secrets, deny, laws,
# runtime tests, dashboard UI) at the same time; the second lane's log
# prints when it ends.
#
# CI_LOCAL_SECRETS_RANGE: the `git log` range that full and pre-push scan
# for secrets. Default: origin/main..HEAD.
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

# A change as ci_pr_crates.py rows: `<path>` TAB `<old path>`, from `git
# diff --name-status` with the arguments given (--cached, or two commits).
change_rows() {
  git diff --name-status -M --no-color "$@" | awk -F'\t' '
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

# A path no crate builds or tests from: the gate tooling, the GitHub and Nix
# files, the agent rules and docs/. (scripts/release/ and README.md stay
# code: eukhe-cli's packaging tests run and copy them.)
outside_crates() {
  case "$1" in
    "" | .github/* | nix/* | docs/* | scripts/ci_* | scripts/test_ci_* | \
      .pre-commit-config.yaml | .gitleaks.toml | AGENTS.md | Makefile | flake.nix | flake.lock) return 0 ;;
    *) return 1 ;;
  esac
}

# The crates a change touches and their reverse dependencies
# (scripts/ci_pr_crates.py), as cargo arguments in SELECTED: `-p <crate>`
# each, or `--workspace` for another path outside crates/<crate>/. Empty for
# no change, a docs-only change, or paths no crate builds or tests from.
select_crates() {
  local rows="$1" out crates kept="" path old
  SELECTED=()
  if [[ -z "${rows}" ]]; then
    echo "no change"
    return 0
  fi
  if cut -f1,2 <<<"${rows}" | tr '\t' '\n' | docs_only; then
    echo "docs-only change (Markdown in docs/ or at the root)"
    return 0
  fi
  while IFS=$'\t' read -r path old; do
    outside_crates "${path}" && outside_crates "${old}" && continue
    kept+="${path}"$'\t'"${old}"$'\n'
  done <<<"${rows}"
  if [[ -z "${kept}" ]]; then
    echo "no crate builds or tests from the changed paths"
    return 0
  fi
  rows="${kept%$'\n'}"
  out="$(mktemp)"
  GITHUB_OUTPUT="${out}" python3 scripts/ci_pr_crates.py <<<"${rows}"
  crates="$(sed -n 's/^crates=//p' "${out}")"
  rm -f "${out}"
  if [[ -z "${crates}" ]]; then
    SELECTED=(--workspace)
  else
    for crate in ${crates//,/ }; do SELECTED+=(-p "${crate}"); done
  fi
}

clippy_touched() {
  select_crates "$1"
  [[ ${#SELECTED[@]} -eq 0 ]] && { echo "clippy skipped"; return 0; }
  cargo clippy "${SELECTED[@]}" --all-targets --locked -- -D warnings
}

tests_touched() {
  select_crates "$1"
  [[ ${#SELECTED[@]} -eq 0 ]] && { echo "tests skipped"; return 0; }
  # The e2e tests run the other workspace binaries from target/debug, which
  # `cargo test -p` does not rebuild: a stale one tests old code.
  clean_env cargo build --workspace --bins --locked
  clean_env cargo test "${SELECTED[@]}" --locked --no-fail-fast
}

proofs() {
  local out
  out="$(mktemp)"
  python3 scripts/check_laws_wired.py .
  python3 scripts/bend_core.py check
  bend PROOF.bend | tee "${out}"
  grep -qx 'ALL PROOFS CHECK' "${out}"
  rm -f "${out}"
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
  python3 scripts/bend_core.py check
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
  # The JSON lines name each test executable: the shards run them, never
  # `cargo test -p`, which would relink the shared binaries under them.
  clean_env cargo test --workspace --locked --no-run --message-format=json-render-diagnostics >"${dir}/artifacts.jsonl"
  clean_env cargo build --workspace --bins --locked
  echo "running ${total} test shards at the same time (logs: ${dir})"
  for shard in $(seq 1 "${total}"); do
    (trap - INT; clean_env python3 scripts/ci_test_shard.py --shard "${shard}" --total "${total}" \
      --artifacts "${dir}/artifacts.jsonl" --manifest "${dir}/shard-manifest-${shard}.json") </dev/null >"${dir}/shard-${shard}.log" 2>&1 &
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
    gate "clippy (touched crates)" clippy_touched "$(change_rows --cached)"
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
    unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
    # The gates check this worktree, so it must be the pushed commit.
    if [[ "$(git rev-parse HEAD)" != "$(git rev-parse "${to}^{commit}")" ]]; then
      echo "pre-push: the push sends ${to:0:12}, but this worktree is at $(git rev-parse --short=12 HEAD). Push from a worktree at the pushed commit." >&2
      exit 1
    fi
    if [[ -n "${from}" && ! "${from}" =~ ^0+$ ]] && git cat-file -e "${from}^{commit}" 2>/dev/null; then
      base="${from}"
    else
      base="$(git merge-base "${to}" "${PRE_COMMIT_REMOTE_NAME:-origin}/main")"
    fi
    rows="$(change_rows "${base}" "${to}")"
    echo "pre-push: ${base:0:12}..${to:0:12}"
    gate "bend version" check_bend
    gate fmt cargo fmt --all --check
    CI_LOCAL_SECRETS_RANGE="${base}..${to}" gate secrets secrets_range
    gate "clippy (touched crates)" clippy_touched "${rows}"
    gate proofs proofs
    gate "tests (touched crates)" tests_touched "${rows}"
    ;;
  *)
    echo "usage: scripts/ci_local.sh fast|full|pre-push" >&2
    exit 2
    ;;
esac
