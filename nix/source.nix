# eukhe built from source, in the same layout as the prebuilt release (see
# package.nix): the binary, its Python runtime, the bundled skills, and the
# bundled catalog: the models asset made from the pinned models.dev snapshot
# kept in the repository, the MCP services from the repository's services
# fixture (the build has no network; eukhe reads only the bundled catalog
# and its compiled-in fallback, and never fetches one). A source build is no
# release: it reports <workspace version>-dev (eukhe-build-info), and so does
# its package version.
{
  lib,
  rustPlatform,
  python3,
  makeWrapper,
  git,
  onnxruntime,
  stdenv,
  src,
  # The source revision (flake `self.rev`/`self.dirtyRev`), compiled into the
  # build identity: the flake source carries no .git for the build to ask.
  commit ? null,
}:
rustPlatform.buildRustPackage {
  pname = "eukhe";
  version = (lib.importTOML (src + "/Cargo.toml")).workspace.package.version + "-dev";
  inherit src;
  env = lib.optionalAttrs (commit != null) { EUKHE_BUILD_COMMIT = commit; };

  # The one git dependency, crossterm's fork (root Cargo.toml
  # [patch.crates-io]), is pinned by commit in Cargo.lock and by hash here.
  cargoLock = {
    lockFile = src + "/Cargo.lock";
    outputHashes."crossterm-0.28.1" = "sha256-eExH/+FlZYaJEVZhHtHLWU5XLJaZEm9LLEpy+8c/WuM=";
  };
  cargoBuildFlags = [
    "-p"
    "eukhe-cli"
    "--bin"
    "eukhe"
  ];
  # The suites need network, sockets and uv (the tests' kernel venv).
  doCheck = false;

  nativeBuildInputs = [
    python3
    makeWrapper
  ];

  postInstall = ''
    payload="$out/libexec/eukhe"
    mkdir -p "$payload/eukhe-runtime"
    mv "$out/bin/eukhe" "$payload/"
    cp -R eukhe-runtime/pyproject.toml eukhe-runtime/requirements-kernel.txt eukhe-runtime/src "$payload/eukhe-runtime/"
    cp -R skills "$payload/skills"
    cp LICENSE "$payload/"
    catalog="$(mktemp -d)"
    mkdir -p "$catalog/plugins"
    cp crates/eukhe-core/tests/fixtures/mcp/plugins-catalog.v2.json "$catalog/plugins/catalog.v2.json"
    python3 scripts/release/bundle_catalog.py generate --catalog-dir "$catalog" --out "$payload"
    rm -r "$catalog"
    # git commits the chat memory after every turn; a user's own git
    # earlier on PATH wins. The Python kernel needs nothing on PATH: eukhe
    # fetches its own pinned uv and Python. The tiny-model worker loads
    # ONNX Runtime (>= 1.24) at run time; a user's own ORT_DYLIB_PATH wins.
    makeWrapper "$payload/eukhe" "$out/bin/eukhe" \
      --suffix PATH : ${lib.makeBinPath [ git ]} \
      --set-default ORT_DYLIB_PATH ${lib.getLib onnxruntime}/lib/libonnxruntime${stdenv.hostPlatform.extensions.sharedLibrary}
  '';

  meta = {
    description = "Eukhe agent harness (from source)";
    homepage = "https://github.com/gildrb/eukhe";
    license = lib.licenses.mit;
    mainProgram = "eukhe";
  };
}
