# NixOS module: `programs.eukhe`. The package for every user, and nix-ld:
# the Python kernel runs on one pinned standalone CPython that eukhe fetches
# on first use (~/.eukhe/kernel), a generic Linux build that needs the
# /lib64 loader NixOS does not have. Without nix-ld the `python` tool fails.
self:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.programs.eukhe;
in
{
  options.programs.eukhe = {
    enable = lib.mkEnableOption "the Eukhe agent harness for every user";

    package = lib.mkOption {
      type = lib.types.package;
      default = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
      defaultText = lib.literalExpression "eukhe.packages.\${system}.default";
      description = "The eukhe package to install system-wide.";
    };
  };

  config = lib.mkIf cfg.enable {
    environment.systemPackages = [ cfg.package ];
    # A default: `programs.nix-ld.enable = false;` turns it off (and the
    # Python kernel with it).
    programs.nix-ld.enable = lib.mkDefault true;
  };
}
