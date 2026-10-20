# Develop

```sh
nix develop        # Rust toolchain, uv, git, ONNX Runtime (sets ORT_DYLIB_PATH)
make check         # fmt, clippy, tests
make dashboard-ui  # Node: rebuild the dashboard web app into crates/eukhe-dashboard/web (commit it)
```

Run tests with a clean environment. Inherited `EUKHE_*` variables point
test daemons at real state:

```sh
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace
```

## Releases

Every commit of `main` that passes CI (`.github/workflows/ci.yml`: the
laws, the tests, the deny gate) is released once, by
`.github/workflows/eukhe-release.yml`. The version is the next patch of
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
