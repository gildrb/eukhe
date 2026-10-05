# eukhe built from source, in the same layout as the prebuilt release (see
# package.nix): the binary, its Python runtime, the bundled skills, and the
# catalog snapshot kept in the repository (the build has no network; the
# binary refreshes the catalog at runtime).
{
  lib,
  rustPlatform,
  python3,
  makeWrapper,
  uv,
  git,
  src,
}:
rustPlatform.buildRustPackage {
  pname = "eukhe";
  version = (lib.importTOML (src + "/Cargo.toml")).workspace.package.version;
  inherit src;

  # No git dependencies; vendor/crossterm is a path patch inside the source.
  cargoLock.lockFile = src + "/Cargo.lock";
  cargoBuildFlags = [
    "-p"
    "eukhe-cli"
    "--bin"
    "eukhe"
  ];
  # The suites need network, sockets, Python, and uv.
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
    mkdir -p "$catalog/models" "$catalog/plugins"
    cp crates/eukhe-models/tests/fixtures/catalog.v1.json "$catalog/models/catalog.v1.json"
    cp crates/eukhe-core/tests/fixtures/mcp/plugins-catalog.v2.json "$catalog/plugins/catalog.v2.json"
    python3 scripts/release/bundle_catalog.py generate --catalog-dir "$catalog" --out "$payload"
    rm -r "$catalog"
    makeWrapper "$payload/eukhe" "$out/bin/eukhe" \
      --suffix PATH : ${
        lib.makeBinPath [
          uv
          git
        ]
      } \
      --set-default EUKHE_TELEMETRY 0
  '';

  meta = {
    description = "A coding agent with one endless chat as its memory (from source)";
    homepage = "https://github.com/gildrb/eukhe";
    license = lib.licenses.mit;
    mainProgram = "eukhe";
  };
}
