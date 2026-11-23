# eukhe built from source, in the same layout as the prebuilt release (see
# package.nix): the binary, its Python runtime, the bundled skills, and the
# bundled model catalog made from the pinned models.dev snapshot kept in the
# repository (the build has no network; eukhe reads only the bundled catalog
# and its compiled-in fallback, and never fetches one). A source build is no
# release: it reports <workspace version>-dev (eukhe-build-info), and so does
# its package version.
{
  lib,
  rustPlatform,
  python3,
  python314,
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
    outputHashes."crossterm-0.28.1" = "sha256-E0HlWhiJiaINnY3ev05AHKOwEV8VI4D/GCbHSEwmqSo=";
  };
  # The shipping profile of the release builds (root Cargo.toml [profile.dist]).
  buildType = "dist";
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
    mkdir -p "$payload/rlm"
    mv "$out/bin/eukhe" "$payload/"
    cp -R rlm/pyproject.toml rlm/requirements-kernel.txt rlm/src "$payload/rlm/"
    cp -R skills "$payload/skills"
    cp LICENSE THIRD-PARTY-NOTICES "$payload/"
    python3 .github/scripts/release/bundle_catalog.py generate --out "$payload"
    ${import ./kernel-bytecode.nix { inherit lib python314; } "$payload"}
    # git commits the chat memory after every turn; a user's own git
    # earlier on PATH wins. The Python kernel needs nothing on PATH: eukhe
    # fetches its own pinned uv and Python. The tiny-model worker loads
    # ONNX Runtime (>= 1.24) at run time; a user's own ORT_DYLIB_PATH wins.
    makeWrapper "$payload/eukhe" "$out/bin/eukhe" \
      --suffix PATH : ${lib.makeBinPath [ git ]} \
      --set-default ORT_DYLIB_PATH ${lib.getLib onnxruntime}/lib/libonnxruntime${stdenv.hostPlatform.extensions.sharedLibrary}
  '';

  meta = {
    description = "A harness and embeddable core for agents that work toward a goal, within limits, until checks pass";
    homepage = "https://github.com/gildrb/eukhe";
    license = lib.licenses.asl20;
    mainProgram = "eukhe";
    platforms = lib.platforms.linux ++ lib.platforms.darwin;
  };
}
