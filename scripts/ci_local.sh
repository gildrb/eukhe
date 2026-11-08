#!/usr/bin/env bash
# The CI gates of eukhe. They run only here: GitHub runs
# no gate. prek runs fast and pre-push as git hooks
# (.pre-commit-config.yaml; `make hooks` installs them); the nightly run
# (scripts/ci_nightly.sh) runs full and releases only when it passes.
#
#   scripts/ci_local.sh fast      `make ci-fast`, the pre-commit gate
#                                 (< 1 min): rustfmt, the crate layering
#                                 (scripts/check_crate_layers.py), the
#                                 secrets scan of the staged diff, and
#                                 clippy on the crates the staged change
#                                 touches.
#   scripts/ci_local.sh pre-push  the pre-push gate (< 5 min), on the pushed
#                                 commits (PRE_COMMIT_FROM_REF..
#                                 PRE_COMMIT_TO_REF, from prek), in this
#                                 worktree: rustfmt, their secrets scan,
#                                 clippy and the unit tests (nextest profile
#                                 pre-push: no e2e suite) of the crates they
#                                 touch, the proofs their Bend change can
#                                 reach (scripts/bend_proofs.py), and the
#                                 laws against LAWS.lock. No lock: every
#                                 worktree pushes at any time.
#   scripts/ci_local.sh full      `make ci-local`, the nightly gate
#                                 (< 30 min): everything, on the current
#                                 tree: every test (nextest profile
#                                 nightly, and the doctests), `bend
#                                 PROOF.bend --verdict`.
#   scripts/ci_local.sh lock      `make lock`: re-lock the laws in seconds.
#                                 The proofs the change since origin/main
#                                 can reach, then LAWS.lock written.
#
# Each gate prints its name; a failed gate prints `ci-<mode>: gate <name>
# FAILED` and the script stops with its exit code. The full gate runs the
# Rust lane (clippy, tests) and the other lane (secrets, deny, laws,
# runtime tests, dashboard UI) at the same time; the second lane's log
# prints when it ends.
#
# A failed test runs once more (.config/nextest.toml, retries = 1): a pass
# then is flaky, named as `  flaky: <test>`, and does not fail the gate (the
# nightly summary keeps the names, so the timing bug gets fixed); a second
# failure fails it.
#
# The tools and the build environment (cargo-nextest, sccache) come
# from mise.toml: the script trusts, installs and loads it.
#
# CI_LOCAL_SECRETS_RANGE: the `git log` range that full and pre-push scan
# for secrets. Default: origin/main..HEAD.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:?usage: scripts/ci_local.sh fast|pre-push|full|lock}"
if [[ -f mise.toml ]] && command -v mise >/dev/null 2>&1; then
  mise trust --quiet mise.toml
  mise install --quiet
  eval "$(mise env --shell bash)"
fi
unset RUSTUP_TOOLCHAIN
export BEND_NO_TELEMETRY=1
# BEND_VERSION and LEAN_VERSION.
# shellcheck source=scripts/toolchain.env
source scripts/toolchain.env
# The pinned Bend (scripts/pinned_bend.sh) leads PATH, and BEND_BIN names
# it for scripts/bend_core.py and scripts/bend_proofs.py (a mise python3
# shim rewrites PATH), so every gate runs it whatever a version manager's
# default is. check_bend fails, naming the version, without it.
if BEND_BIN="$(scripts/pinned_bend.sh 2>/dev/null)"; then
  PATH="$(dirname "${BEND_BIN}"):${PATH}"
  export PATH BEND_BIN
fi

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
  scripts/pinned_bend.sh >/dev/null
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
  [[ ${#missing[@]} -eq 0 ]] || { echo "not installed: ${missing[*]} (mise.toml and nix develop have them)"; return 1; }
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
# files, the agent rules, docs/, and the laws and proofs (the proofs gate
# checks them). (scripts/release/ and
# README.md stay code: eukhe-cli's packaging tests run and copy them.)
outside_crates() {
  case "$1" in
    "" | .github/* | nix/* | docs/* | scripts/ci_* | scripts/test_ci_* | \
      scripts/bend_proofs.py | scripts/test_bend_proofs.py | .config/nextest.toml | mise.toml | \
      .pre-commit-config.yaml | .gitleaks.toml | AGENTS.md | Makefile | flake.nix | flake.lock | \
      LAWS.bend | PROOF.bend | LAWS.lock | laws/* | proof/*) return 0 ;;
    *) return 1 ;;
  esac
}

# A change the proofs gate must check: a Bend file, the generated core and
# its entry list, or the scripts and toolchain pin the gate runs.
bend_touched() {
  local path old p
  while IFS=$'\t' read -r path old; do
    for p in "${path}" "${old}"; do
      case "${p}" in
        *.bend | bend/* | crates/eukhe-bend/* | scripts/bend_core.py | scripts/bend_proofs.py | \
          scripts/check_laws_wired.py | scripts/pinned_bend.sh | scripts/toolchain.env) return 0 ;;
      esac
    done
  done <<<"$1"
  return 1
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

# The cargo target arguments of the unit tests of the packages SELECTED
# names: --lib, --bins, and --test for each integration test target that
# is not an e2e suite (named *_e2e, .config/nextest.toml). The e2e binaries
# that pre-push does not run are not built either.
unit_targets() {
  local crates=() arg
  for arg in "${SELECTED[@]}"; do
    [[ "${arg}" == -p || "${arg}" == --workspace ]] || crates+=("${arg}")
  done
  printf '%s\n' --lib --bins
  cargo metadata --no-deps --format-version 1 --locked | python3 -c '
import json, sys
want = set(sys.argv[1:])
for p in json.load(sys.stdin)["packages"]:
    if want and p["name"] not in want:
        continue
    for t in p["targets"]:
        if "test" in t["kind"] and t.get("test", True) and not t["name"].endswith("_e2e"):
            print("--test")
            print(t["name"])
' "${crates[@]}"
}

tests_touched() {
  local out targets
  select_crates "$1"
  [[ ${#SELECTED[@]} -eq 0 ]] && { echo "tests skipped"; return 0; }
  out="$(unit_targets)"
  mapfile -t targets <<<"${out}"
  clean_env cargo nextest run "${SELECTED[@]}" "${targets[@]}" --locked --profile pre-push --no-tests=pass
}

# The proofs a Bend change can reach (scripts/bend_proofs.py: the proof
# files whose import closure holds a changed file), from the commit $2.
proofs() {
  if ! bend_touched "$1"; then
    echo "proofs skipped: no Bend input changed"
    return 0
  fi
  python3 scripts/check_laws_wired.py .
  python3 scripts/bend_core.py check
  python3 scripts/bend_proofs.py --base "$2"
}

# The laws against the committed LAWS.lock (the bend skill's `gate.py
# --lock-only`, seconds), when a law, a spec helper or the lock changed: a
# law changed without the user's re-lock fails here. BEND_SKILL: the skill
# directory (default ~/.agents/skills/bend).
BEND_SKILL="${BEND_SKILL:-${HOME}/.agents/skills/bend}"
laws_lock() {
  local path old p hit=1
  while IFS=$'\t' read -r path old; do
    for p in "${path}" "${old}"; do
      case "${p}" in
        LAWS.bend | LAWS.lock | laws/* | spec/*) hit=0 ;;
      esac
    done
  done <<<"$1"
  if (( hit )); then
    echo "lock skipped: no law or lock changed"
    return 0
  fi
  python3 "${BEND_SKILL}/scripts/gate.py" . --lock-only
}

# `make lock`: the proofs the change since origin/main can reach
# (scripts/bend_proofs.py), then LAWS.lock written from the laws (`gate.py
# --lock-only --lock`: no checker run). The nightly gate proves everything
# and runs --verdict.
relock() {
  python3 scripts/check_laws_wired.py .
  python3 scripts/bend_proofs.py --base "$(git merge-base HEAD origin/main)"
  python3 "${BEND_SKILL}/scripts/gate.py" . --lock-only --lock
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
  bend PROOF.bend --verdict | tee "${out}/verdict.out"
  grep -qx 'ALL PROOFS CHECK' "${out}/verdict.out"
  rm -rf "${out}"
}

dashboard_ui() {
  make --no-print-directory dashboard-ui
  git diff --exit-code --stat -- crates/eukhe-dashboard/web
  test -z "$(git status --porcelain -- crates/eukhe-dashboard/web)"
}

# The test environment is clean (AGENTS.md: inherited EUKHE_* variables
# would point test daemons at real state), except for the build settings
# (cargo's, rustup's, sccache's; mise.toml), so the tests reuse the build
# the other gates made.
clean_env() {
  local keep=() name
  for name in $(compgen -e); do
    case "${name}" in
      CARGO_* | RUSTUP_* | RUSTFLAGS | RUSTDOCFLAGS | RUSTC_WRAPPER | SCCACHE_*) keep+=("${name}=${!name}") ;;
    esac
  done
  env -i HOME="${HOME}" PATH="${PATH}" USER="${USER:-}" LANG="${LANG:-C.UTF-8}" \
    BEND_NO_TELEMETRY=1 "${keep[@]}" "$@"
}

# Every test: nextest profile nightly (every binary at once on one build;
# the e2e suites and the self-serializing tests in their test groups,
# .config/nextest.toml), then the doctests, which nextest does not run.
# The flaky tests (a failure, then a pass on the retry) are named from the
# JUnit report.
workspace_tests() {
  local rc=0
  clean_env cargo nextest run --workspace --locked --profile nightly || rc=$?
  [[ -f target/nextest/nightly/junit.xml ]] && python3 - target/nextest/nightly/junit.xml <<'EOF'
import sys
import xml.etree.ElementTree as ET

for case in ET.parse(sys.argv[1]).iter("testcase"):
    if case.find("flakyFailure") is not None or case.find("flakyError") is not None:
        print(f"  flaky: {case.get('classname')} {case.get('name')}")
EOF
  (( rc == 0 )) || return "${rc}"
  clean_env cargo test --workspace --doc --locked
}

side_lane() {
  gate secrets secrets_range
  gate deny make --no-print-directory deny
  gate laws laws
  gate runtime-test make --no-print-directory runtime-test
  gate nix-test make --no-print-directory nix-test
  gate dashboard-ui dashboard_ui
}

case "${mode}" in
  fast)
    gate "bend version" check_bend
    gate fmt cargo fmt --all --check
    gate "crate layers" python3 scripts/check_crate_layers.py .
    gate secrets secrets_staged
    gate "clippy (touched crates)" clippy_touched "$(change_rows --cached)"
    ;;
  full)
    # The full gate builds the workspace once: incremental files only add
    # size, and a non-incremental build is one sccache keeps (the nightly
    # worktree's path is the same every night). clean_env passes it on.
    export CARGO_INCREMENTAL=0
    start=${SECONDS}
    gate tools check_tools cargo cargo-nextest uv npm python3 cargo-deny jq
    gate "bend version" check_bend
    gate "lean version" check_lean
    gate fmt cargo fmt --all --check
    gate "crate layers" python3 scripts/check_crate_layers.py .
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
      gate clippy cargo clippy --workspace --all-targets --locked -- -D warnings
      gate test workspace_tests
    )
    rust_rc=$?
    wait "${side}"
    side_rc=$?
    set -e
    echo "==> ci-full: secrets, deny, laws, runtime-test, nix-test, dashboard-ui log"
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
    # A push to a branch other than main (an integration branch) stops here:
    # main's push runs the rest once, when the branch merges.
    if [[ -n "${PRE_COMMIT_REMOTE_BRANCH:-}" && "${PRE_COMMIT_REMOTE_BRANCH}" != "refs/heads/main" ]]; then
      echo "pre-push: ${PRE_COMMIT_REMOTE_BRANCH} is not main: clippy, proofs, lock and tests run when it merges into main"
      exit 0
    fi
    gate "clippy (touched crates)" clippy_touched "${rows}"
    gate proofs proofs "${rows}" "${base}"
    gate "laws lock" laws_lock "${rows}"
    gate "tests (touched crates)" tests_touched "${rows}"
    ;;
  lock)
    gate "bend version" check_bend
    gate relock relock
    ;;
  *)
    echo "usage: scripts/ci_local.sh fast|pre-push|full|lock" >&2
    exit 2
    ;;
esac
