# The prebuilt eukhe release for one system (see ../flake.nix): the
# archive the release workflow published, patched for Nix, with `eukhe` as
# its command. The payload keeps the archive's layout under libexec: the
# binary finds its Python runtime and bundled skills next to itself.
{
  lib,
  stdenv,
  fetchurl,
  autoPatchelfHook,
  makeWrapper,
  uv,
  git,
  release,
}:
let
  system = stdenv.hostPlatform.system;
  asset =
    release.assets.${system}
      or (throw "eukhe ${release.version}: no prebuilt release for ${system}; use packages.${system}.eukhe-from-source");
in
stdenv.mkDerivation {
  pname = "eukhe";
  inherit (release) version;

  src = fetchurl { inherit (asset) url hash; };
  # The archive's files sit at its root.
  sourceRoot = ".";

  nativeBuildInputs = [
    makeWrapper
  ]
  ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
  # The Linux binary needs libgcc_s besides glibc; TLS is rustls with built-in roots.
  buildInputs = lib.optionals stdenv.hostPlatform.isLinux [ stdenv.cc.cc.lib ];

  dontConfigure = true;
  dontBuild = true;
  # Already stripped of debug info; a macOS binary keeps its signature.
  dontStrip = true;

  installPhase = ''
    runHook preInstall
    payload="$out/libexec/eukhe"
    mkdir -p "$payload" "$out/bin"
    cp -R prime-agent prime-agent-runtime skills LICENSE "$payload/"
    for file in models.bundled.json mcp-services.bundled.json package.json; do
      if [ -e "$file" ]; then
        cp "$file" "$payload/"
      fi
    done
    # uv builds the Python kernel's venv; git commits the chat memory after
    # every turn. A user's own uv or git earlier on PATH wins.
    makeWrapper "$payload/prime-agent" "$out/bin/eukhe" \
      --suffix PATH : ${
        lib.makeBinPath [
          uv
          git
        ]
      } \
      --set-default PRIME_AGENT_TELEMETRY 0
    runHook postInstall
  '';

  meta = {
    description = "Prime Agent with one endless chat as its memory (prebuilt)";
    homepage = "https://github.com/gildrb/eukhe";
    license = lib.licenses.mit;
    mainProgram = "eukhe";
    platforms = builtins.attrNames release.assets;
    sourceProvenance = [ lib.sourceTypes.binaryNativeCode ];
  };
}
