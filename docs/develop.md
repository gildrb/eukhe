# Develop

```sh
nix develop        # Rust toolchain, uv, git, ONNX Runtime (sets ORT_DYLIB_PATH)
make check         # fmt, clippy, tests
make dashboard-ui  # Node: rebuild the dashboard web app into crates/eukhe-dashboard/web (commit it)
make hooks         # install the git hooks (prek)
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace  # clean env: inherited EUKHE_* points test daemons at real state
```

## Local CI and git hooks

Gates run only here, in git hooks. GitHub runs no gate; no pull requests.

```sh
mise use -g github:j178/prek@0.5.7  # prek 0.5.7 (https://github.com/j178/prek)
make hooks   # prek install --allow-missing-config --hook-type pre-commit --hook-type pre-push
```

Hooks (`.pre-commit-config.yaml`) run under `nice -n 10` and unset `RUSTUP_TOOLCHAIN` (`rust-toolchain.toml` selects).

|Hook|Command|Checks|
|---|---|---|
|pre-commit|`make ci-fast`|Staged change: `cargo fmt`; gitleaks on the staged diff (skipped with a note if not installed); clippy `-D warnings` on touched crates + dependents (`scripts/ci_pr_crates.py`; a path outside `crates/<crate>/` selects the workspace)|
|pre-push|`scripts/ci_local.sh pre-push`|Pushed commits, in the pushing worktree: `cargo fmt`; gitleaks on them; clippy and `cargo test --no-fail-fast` on touched crates + dependents (`laws/`, `proof/`, `LAWS.bend`, `PROOF.bend`, `LAWS.lock`, docs, CI and agent files select no crate); `scripts/check_laws_wired.py`, `bend_core.py check` and `bend PROOF.bend` only when a Bend input changed (`*.bend`, `bend/`, `crates/eukhe-bend/`, the gate scripts, `scripts/toolchain.env`); `gate.py --lock-only` of the bend skill (`$BEND_SKILL`, default `~/.agents/skills/bend`) when a law or `LAWS.lock` changed|

- Push from a worktree at the pushed commit. No lock; any worktree pushes any time.
- Skip: a push changing only Markdown in `docs/` or the repo root skips pre-push.
- Needs bend and Lean at `scripts/toolchain.env` versions, cargo-deny, uv, npm, gitleaks.
- A failed gate prints its name; fix, rerun.

## Nightly gate

A systemd user timer runs `scripts/ci_nightly.sh run` at 02:30 UTC: full gate (`make ci-local`) on `origin/main` in the gate worktree (`<repo>-ci` beside the checkout, e.g. `~/Repos/eukhe-ci`).

Full gate: fmt; workspace cargo check and clippy; every test unit in 8 parallel shards, clean env, `EUKHE_REQUIRE_BEND=1`; eukhe-runtime suite; dashboard UI (`web/` up to date); `bend PROOF.bend` and `--verdict`; cargo-deny; gitleaks on commits since the last release.

- Green: releases that commit (`gh workflow run eukhe-release.yml -f sha=<commit>`).
- Red: no release; a test-breaking commit never ships.

| Build-size rule | Why |
| --- | --- |
| Each nightly run starts with `cargo clean` in the gate worktree | Cargo never deletes stale build files; one day of runs grew the build dir to 410 GB |
| Full gate: `CARGO_INCREMENTAL=0` | One build; incremental files only add size |
| Full gate: `CARGO_PROFILE_DEV_DEBUG=line-tables-only` | Failed tests still show file and line; full debug info is several times larger |
| Tests keep these two settings | Tests reuse the gate's build; other settings double the size |

```sh
make nightly          # run the nightly gate now
make nightly-status   # result of the last run
```

- `~/.eukhe/ci/nightly.log`: each run's result; on failure, failed gates and test units.
- `~/.eukhe/ci/nightly-last.log`: full output of the last run.

GitHub runs one workflow: the release.

## Releases

- The nightly gate starts `.github/workflows/eukhe-release.yml` for the passing commit. Urgent release of a commit that passed `make ci-local`: run it by hand (`workflow_dispatch` with `sha`).
- Version: next patch of the `Cargo.toml` series (`[workspace.package] version = "X.Y.0"`): 1 + highest patch among tags `eukhe-vX.Y.P`, or 0 for a series' first release.
- Tag `eukhe-v<version>`, title `Eukhe v<version>`, marked latest, pinned for the flake in `nix/release.json`.
- New series: set the workspace version to the next `X.Y.0` (e.g. `0.11.0`, `1.0.0`).
- Stops the release: a workspace version not `X.Y.0`, a tag of a newer series, or a version number of more than 6 digits.
- `eukhe-next-version` (crate `eukhe-build-info`) computes it: the rule `bend/semver.bend` runs as compiled Bend (entry `bend/ffi_semver.bend`, `eukhe_bend::rules::semver`); laws `laws/semver.bend` (R1 the rule, R2 the entry), proved in `PROOF.bend`. The build script checks `EUKHE_RELEASE_VERSION` with the same rule.
