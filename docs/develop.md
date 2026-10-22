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

The full CI gate runs on this machine, not on GitHub. Install
[prek](https://github.com/j178/prek) 0.5.7, then the hooks:

```sh
mise use -g github:j178/prek@0.5.7
make hooks   # prek install --allow-missing-config --hook-type pre-commit --hook-type pre-push
```

The hooks (`.pre-commit-config.yaml`) run at low CPU priority
(`nice -n 10`) on all cores. They unset `RUSTUP_TOOLCHAIN`, so
`rust-toolchain.toml` selects the toolchain.

- pre-commit: `make ci-fast`. It checks the staged change: `cargo fmt`,
  a gitleaks scan of the staged diff (skipped with a note when gitleaks
  is not installed), and clippy `-D warnings` on the crates the change
  touches and their dependents (`scripts/ci_pr_crates.py`; a path
  outside `crates/<crate>/` selects the workspace).
- pre-push: `make ci-local` on the pushed commit, in a separate worktree
  (`<git common dir>/eukhe-ci-local`), so local changes do not change the
  result. It runs every gate of `.github/workflows/ci.yml`: fmt, cargo
  check and clippy, `cargo test --workspace` in a clean environment with
  `EUKHE_REQUIRE_BEND=1`, the eukhe-runtime suite, the dashboard UI
  (`web/` up to date), `bend PROOF.bend` and `--verdict`,
  `scripts/check_laws_wired.py`, the release-version bridge, cargo-deny,
  and gitleaks on the pushed commits.
- Skip rule: a push that changes only Markdown files in `docs/` or at
  the repository root does not run the pre-push gate.

The gates need bend and Lean at the versions that
`.github/actions/setup-bend` pins, and cargo-deny, uv, npm and gitleaks.
A gate that fails prints its name; fix the cause and run the command
again.

On GitHub, a push to main runs only fmt, cargo-deny, the secrets scan and
the laws. Pull requests, the merge queue and `workflow_dispatch` run the
full gate.

## Releases

Once a day (03:17 UTC), `.github/workflows/eukhe-release.yml` releases
the newest commit of `main` whose `ci.yml` push run passed and that has
no `eukhe-v*` tag. Run the workflow by hand (`workflow_dispatch`) for an
urgent release. The version is the next patch of
the series in `Cargo.toml` (`[workspace.package] version = "X.Y.0"`): 1 +
the highest patch among the tags `eukhe-vX.Y.P`, or 0 for the first
release of a series. The release is tagged `eukhe-v<version>`, titled
`Eukhe v<version>`, marked latest, and pinned for the flake in
`nix/release.json`. To start a new series, set the workspace version to
the next `X.Y.0` (for example `0.11.0` or `1.0.0`). A workspace version
that is no `X.Y.0`, or a tag of a newer series, stops the release.
`scripts/release/next_version.py` computes the version; its rule is the
model `bend/semver.bend`, whose laws (`laws/release.bend`, section R1)
`PROOF.bend` proves, and `scripts/release/test_next_version.py` runs the
script and the model on the same cases.
