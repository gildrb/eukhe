# The Bend release scripts/toolchain.env pins (BEND_VERSION, the single
# pin), for the dev shell: the gates run `bend PROOF.bend`, `bend
# --verdict` and `make bend-core` with exactly this release
# (scripts/pinned_bend.sh). The release archive is the `bend/` tree:
# `bin/bend` beside the libraries it reads, kept together under libexec.
# A new BEND_VERSION fails the fetch here until `hashes` names its archives.
{
  lib,
  stdenv,
  fetchurl,
  autoPatchelfHook,
}:
let
  version = lib.removePrefix "BEND_VERSION=" (
    lib.findFirst (lib.hasPrefix "BEND_VERSION=") (throw "scripts/toolchain.env sets no BEND_VERSION") (
      lib.splitString "\n" (builtins.readFile ../scripts/toolchain.env)
    )
  );
  hashes = {
    "x86_64-linux" = {
      platform = "linux-x64";
      hash = "sha256-yf+NZ72QP7atmia0PYpiwBAh3oKkTVXOSj3NRzIRPWs=";
    };
    "aarch64-linux" = {
      platform = "linux-arm64";
      hash = "sha256-L0Km+jTs2qca4QXl+nNPmgfhKdMz5FRIq20v8DqDdXA=";
    };
    "aarch64-darwin" = {
      platform = "darwin-arm64";
      hash = "sha256-sr4AOwQets/GUya+GPeesuC64hib55oYxQfmYbS2kAs=";
    };
  };
  asset =
    hashes.${stdenv.hostPlatform.system}
      or (throw "Bend ${version}: no release archive for ${stdenv.hostPlatform.system}");
in
stdenv.mkDerivation {
  pname = "bend";
  inherit version;

  src = fetchurl {
    url = "https://github.com/bendlang/bend/releases/download/v${version}/bend-${version}-${asset.platform}.tar.gz";
    inherit (asset) hash;
  };
  sourceRoot = ".";

  nativeBuildInputs = lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];

  dontConfigure = true;
  dontBuild = true;
  dontStrip = true;

  installPhase = ''
    runHook preInstall
    mkdir -p "$out/libexec" "$out/bin"
    cp -R bend "$out/libexec/bend"
    ln -s "$out/libexec/bend/bin/bend" "$out/bin/bend"
    runHook postInstall
  '';

  meta = {
    description = "Bend ${version}, the release the Eukhe gates pin";
    homepage = "https://github.com/bendlang/bend";
    platforms = builtins.attrNames hashes;
    sourceProvenance = [ lib.sourceTypes.binaryNativeCode ];
    mainProgram = "bend";
  };
}
