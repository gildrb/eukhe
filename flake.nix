{
  description = "A harness and embeddable core for agents that work toward a goal, within limits, until checks pass";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs }:
    let
      inherit (nixpkgs) lib;
      # The release targets this nixpkgs still evaluates.
      systems = builtins.filter (system: nixpkgs.legacyPackages ? ${system}) [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      # Written by .github/workflows/eukhe-release.yml: the newest release's
      # archive URL and SRI hash per system. Empty `assets` (no release in
      # the current layout yet) builds every system from source.
      release = lib.importJSON ./nix/release.json;
    in
    {
      packages = forAllSystems (
        pkgs:
        let
          system = pkgs.stdenv.hostPlatform.system;
          eukhe-from-source = pkgs.callPackage ./nix/source.nix {
            src = self;
            commit = self.rev or self.dirtyRev or null;
          };
          eukhe-prebuilt = pkgs.callPackage ./nix/package.nix { inherit release; };
        in
        {
          inherit eukhe-from-source;
          # The prebuilt release when one exists for this system: nothing
          # to compile. Otherwise the same layout built from source.
          default = if release.assets ? ${system} then eukhe-prebuilt else eukhe-from-source;
          eukhe = self.packages.${system}.default;
        }
        // lib.optionalAttrs (release.assets ? ${system}) { inherit eukhe-prebuilt; }
      );

      apps = forAllSystems (pkgs: {
        default = {
          type = "app";
          program = lib.getExe self.packages.${pkgs.stdenv.hostPlatform.system}.default;
          meta.description = "Run eukhe";
        };
      });

      # The build inputs of the source package plus the tools the suites
      # and the tiny-model worker need at run time.
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          inputsFrom = [ self.packages.${pkgs.stdenv.hostPlatform.system}.eukhe-from-source ];
          packages = [
            pkgs.cargo
            pkgs.rustc
            pkgs.clippy
            pkgs.rustfmt
            pkgs.uv
            pkgs.git
            pkgs.jq
            pkgs.onnxruntime
          ];
          env.ORT_DYLIB_PATH = "${lib.getLib pkgs.onnxruntime}/lib/libonnxruntime${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}";
        };
      });

      overlays.default = final: _prev: {
        eukhe = self.packages.${final.stdenv.hostPlatform.system}.default;
      };

      homeManagerModules.default = import ./nix/home-manager.nix self;
      homeModules.default = self.homeManagerModules.default;
      nixosModules.default = import ./nix/nixos-module.nix self;
    };
}
