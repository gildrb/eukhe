# Develop

```sh
nix develop        # Rust toolchain, uv, git, ONNX Runtime (sets ORT_DYLIB_PATH)
make check         # fmt, clippy, tests
make dashboard-ui  # Node: rebuild the dashboard web app into crates/eukhe-dashboard/web (commit it)
make hooks         # install the git hooks (prek)
```

Run tests with a clean environment. Inherited `EUKHE_*` variables point
test daemons at real state:

```sh
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace
```

## Local CI and git hooks

The CI gates run only on this machine, in the git hooks. GitHub runs no
gate. The repository takes no pull requests. Install
[prek](https://github.com/j178/prek) 0.5.7, then the hooks:

```sh
mise use -g github:j178/prek@0.5.7
make hooks   # prek install --allow-missing-config --hook-type pre-commit --hook-type pre-push
```

The hooks (`.pre-commit-config.yaml`) run at low CPU priority
(`nice -n 10`). They unset `RUSTUP_TOOLCHAIN`, so
`rust-toolchain.toml` selects the toolchain.

- pre-commit: `make ci-fast`. It checks the staged change: `cargo fmt`,
  a gitleaks scan of the staged diff (skipped with a note when gitleaks
  is not installed), and clippy `-D warnings` on the crates the change
  touches and their dependents (`scripts/ci_pr_crates.py`; a path
  outside `crates/<crate>/` selects the workspace).
- pre-push: `scripts/ci_local.sh pre-push`. It checks the pushed commits
  in the worktree that pushes them: `cargo fmt`, a gitleaks scan of the
  pushed commits, clippy and `cargo test --no-fail-fast` on the crates
  they touch and their dependents, `scripts/check_laws_wired.py` and
  `bend PROOF.bend`. Push from a worktree at the pushed commit. There is
  no lock: every worktree pushes at any time.
- Skip rule: a push that changes only Markdown files in `docs/` or at
  the repository root does not run the pre-push gate.

The gates need bend and Lean at the versions that
`scripts/toolchain.env` pins, and cargo-deny, uv, npm and gitleaks.
A gate that fails prints its name; fix the cause and run the command
again.

## Nightly gate

A systemd user timer runs `scripts/ci_nightly.sh run` once a night
(02:30 UTC). It runs the full gate (`make ci-local`) on `origin/main` in
the gate worktree (`<repo>-ci` beside the main checkout, for example
`~/Repos/eukhe-ci`). The full gate is: fmt, cargo check and clippy on the
workspace, every test unit in 8 parallel shards in a clean environment
with `EUKHE_REQUIRE_BEND=1`, the eukhe-runtime suite, the dashboard UI
(`web/` up to date), `bend PROOF.bend` and `--verdict`, the
release-version bridge, cargo-deny, and gitleaks on the commits since the
last release.

- Green: the run starts the release of that commit (`gh workflow run
  eukhe-release.yml -f sha=<commit>`).
- Red: nothing is released. A commit that breaks a test does not ship.

```sh
make nightly          # run the nightly gate now
make nightly-status   # the result of the last run
```

Each run appends its result, and for a failure the failed gates and
test units, to `~/.eukhe/ci/nightly.log`. The full output of the last
run is `~/.eukhe/ci/nightly-last.log`.

GitHub runs one workflow: the release below.

## Releases

The nightly gate starts `.github/workflows/eukhe-release.yml` for the
commit that passed. Run the workflow by hand (`workflow_dispatch` with
`sha`) for an urgent release of a commit that passed `make ci-local`.
The version is the next patch of
the series in `Cargo.toml` (`[workspace.package] version = "X.Y.0"`): 1 +
the highest patch among the tags `eukhe-vX.Y.P`, or 0 for the first
release of a series. The release is tagged `eukhe-v<version>`, titled
`Eukhe v<version>`, marked latest, and pinned for the flake in
`nix/release.json`. To start a new series, set the workspace version to
the next `X.Y.0` (for example `0.11.0` or `1.0.0`). A workspace version
that is no `X.Y.0`, or a tag of a newer series, stops the release.
`scripts/release/next_version.py` computes the version; its rule is the
model `bend/semver.bend`, whose laws (`LAWS.bend` section `release`, section R1)
`PROOF.bend` proves, and `scripts/release/test_next_version.py` runs the
script and the model on the same cases.
