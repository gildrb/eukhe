# eukhe built from source, in the same layout as the prebuilt release (see
# package.nix): the binary, its Python runtime, the bundled skills, and the
# offline catalog fixture.
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
    cp -R eukhe-runtime/pyproject.toml eukhe-runtime/src "$payload/eukhe-runtime/"
    cp -R skills "$payload/skills"
    cp LICENSE "$payload/"
    python3 scripts/release/bundle_catalog.py generate --fixture --out "$payload"
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
