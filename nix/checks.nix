# The flake's checks (`nix flake check`), cheap enough for a gate: nothing
# here downloads a release or compiles eukhe.
#
# - eval: every output of every system evaluates (packages, dev shells,
#   apps, the overlay, the Home Manager module on Linux and macOS, the
#   NixOS module), and what each promises holds: the module installs the
#   package, the daemon is a systemd user service on Linux and a launchd
#   agent on macOS, nixpkgs' rustc is the release rust-toolchain.toml pins.
#   Built on one system, it covers all of them.
# - home-manager: this system's Home Manager generation built with every
#   option set (a stand-in eukhe and signal-cli, so nothing heavy is
#   fetched), and the files it makes read back: ~/.eukhe links, the
#   settings activation, the daemon and gateway units.
{
  self,
  nixpkgs,
  home-manager,
  lib,
  systems,
}:
pkgs:
let
  system = pkgs.stdenv.hostPlatform.system;
  release = lib.importJSON ./release.json;
  rustChannel = (lib.importTOML ../rust-toolchain.toml).toolchain.channel;

  # A Home Manager generation of a throwaway user with `extra` set.
  home =
    hostPkgs: extra:
    home-manager.lib.homeManagerConfiguration {
      pkgs = hostPkgs;
      modules = [
        self.homeManagerModules.default
        {
          home.username = "eukhe-check";
          home.homeDirectory =
            if hostPkgs.stdenv.hostPlatform.isDarwin then "/Users/eukhe-check" else "/home/eukhe-check";
          home.stateVersion = "26.05";
          programs.eukhe.enable = true;
        }
        extra
      ];
    };

  everyOption = hostPkgs: {
    programs.eukhe = {
      settings.memory.thinking = "medium";
      files."AGENTS.md" = hostPkgs.writeText "AGENTS.md" "Rule one.\n";
      daemon.enable = true;
      gateway.enable = hostPkgs.stdenv.hostPlatform.isLinux;
    };
  };

  # What one system's outputs promise, evaluated (never built).
  evalSystem =
    other:
    let
      otherPkgs = nixpkgs.legacyPackages.${other};
      packages = self.packages.${other};
      plain = (home otherPkgs { }).config;
      full = (home otherPkgs (everyOption otherPkgs)).config;
      exe = lib.getExe packages.default;
      nixos = lib.nixosSystem {
        modules = [
          self.nixosModules.default
          {
            nixpkgs.hostPlatform = other;
            programs.eukhe.enable = true;
            boot.loader.grub.enable = false;
            fileSystems."/" = {
              device = "none";
              fsType = "tmpfs";
            };
            system.stateVersion = "26.05";
          }
        ];
      };
      isLinux = otherPkgs.stdenv.hostPlatform.isLinux;
    in
    assert lib.assertMsg (
      packages.default.version == release.version || !(release.assets ? ${other})
    ) "${other}: the default package is not release ${release.version}";
    assert lib.assertMsg (builtins.elem packages.default plain.home.packages)
      "${other}: programs.eukhe.enable does not install the package";
    assert lib.assertMsg (
      if isLinux then
        lib.any (lib.hasPrefix "${exe} --mode daemon") (
          lib.toList full.systemd.user.services.eukhe-daemon.Service.ExecStart
        )
      else
        builtins.elem exe full.launchd.agents.eukhe-daemon.config.ProgramArguments
    ) "${other}: daemon.enable makes no daemon service";
    assert lib.assertMsg (
      !isLinux
      || (
        builtins.elem packages.default nixos.config.environment.systemPackages
        && nixos.config.programs.nix-ld.enable
      )
    ) "${other}: the NixOS module does not install the package with nix-ld";
    map (drv: builtins.unsafeDiscardStringContext drv.drvPath) ([
      packages.default
      packages.eukhe-from-source
      packages.bend
      self.devShells.${other}.default
      full.home.activationPackage
      plain.home.activationPackage
    ])
    ++ [ (builtins.unsafeDiscardStringContext self.apps.${other}.default.program) ];

  stub =
    name:
    (pkgs.writeShellScriptBin name "exit 0").overrideAttrs {
      meta.mainProgram = name;
    };

  built =
    (home pkgs (
      lib.recursiveUpdate (everyOption pkgs) {
        programs.eukhe = {
          package = stub "eukhe";
          gateway.signalCli = stub "signal-cli";
        };
      }
    )).activationPackage;
in
{
  eval =
    assert lib.assertMsg (
      pkgs.rustc.version == rustChannel
    ) "nixpkgs' rustc is ${pkgs.rustc.version}; rust-toolchain.toml pins ${rustChannel}";
    pkgs.writeText "eukhe-eval.json" (builtins.toJSON (lib.genAttrs systems evalSystem));

  home-manager =
    pkgs.runCommand "eukhe-home-manager"
      {
        nativeBuildInputs = [ pkgs.jq ];
      }
      (
        ''
          gen=${built}
          files="$gen/home-files"
          set -x
          grep -qx 'Rule one.' "$files/.eukhe/AGENTS.md"
          grep -q 'eukhe-merge-settings' "$gen/activate"
          settings="$(grep -o '/nix/store/[^ ]*-eukhe-settings.json' "$gen/activate")"
          jq -e '.memory.thinking == "medium"' "$settings"
        ''
        + (
          if pkgs.stdenv.hostPlatform.isLinux then
            ''
              units="$files/.config/systemd/user"
              grep -q -- '--mode daemon' "$units/eukhe-daemon.service"
              grep -q '^Environment=PATH=' "$units/eukhe-daemon.service"
              grep -q ' gateway$' "$units/eukhe-gateway.service"
              grep -q 'signal-cli' "$units/eukhe-gateway.service"
              test -L "$files/.config/systemd/user/default.target.wants/eukhe-daemon.service"
            ''
          else
            ''
              plist="$gen/LaunchAgents/org.nix-community.home.eukhe-daemon.plist"
              grep -q 'DARWIN_USER_TEMP_DIR' "$plist"
              grep -q -- '--mode daemon' "$plist"
              grep -q '/bin/eukhe</string>' "$plist"
            ''
        )
        + ''
          set +x
          touch "$out"
        ''
      );
}
