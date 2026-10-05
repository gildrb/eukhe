# Home Manager module: `programs.eukhe`.
self:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.programs.eukhe;
  json = pkgs.formats.json { };
  stateDir = "${config.home.homeDirectory}/.eukhe";
in
{
  options.programs.eukhe = {
    enable = lib.mkEnableOption "eukhe, a coding agent with one endless chat as its memory";

    package = lib.mkOption {
      type = lib.types.package;
      default = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
      defaultText = lib.literalExpression "eukhe.packages.\${system}.default";
      description = "The eukhe package (the pinned prebuilt release when one exists for the system, else built from source).";
    };

    settings = lib.mkOption {
      type = json.type;
      default = { };
      example = lib.literalExpression ''
        {
          memory = { model = "anthropic/claude-sonnet-5-5"; thinking = "medium"; };
          telemetry.enabled = false;
        }
      '';
      description = ''
        Written to ~/.eukhe/settings.json at activation. eukhe also writes
        this file (model choices), so it is copied, not linked: the declared
        settings win at every activation.
      '';
    };

    files = lib.mkOption {
      type = lib.types.attrsOf lib.types.path;
      default = { };
      example = lib.literalExpression ''{ "AGENTS.md" = ./AGENTS.md; "themes/dusk.json" = ./dusk.json; }'';
      description = "Files linked into ~/.eukhe, by relative path.";
    };

    daemon.enable = lib.mkEnableOption ''
      an always-on eukhe daemon (a systemd user service): sessions survive
      closed terminals, and the chat memory's compactor keeps working while
      no session is open
    '';
  };

  config = lib.mkIf cfg.enable {
    home.packages = [ cfg.package ];

    home.file = lib.mapAttrs' (
      name: source: lib.nameValuePair ".eukhe/${name}" { inherit source; }
    ) cfg.files;

    home.activation.eukheSettings = lib.mkIf (cfg.settings != { }) (
      lib.hm.dag.entryAfter [ "linkGeneration" ] ''
        run ${pkgs.coreutils}/bin/install -D -m 0600 \
          ${json.generate "eukhe-settings.json" cfg.settings} ${lib.escapeShellArg "${stateDir}/settings.json"}
      ''
    );

    systemd.user.services.eukhe-daemon =
      lib.mkIf (cfg.daemon.enable && pkgs.stdenv.hostPlatform.isLinux)
        {
          Unit.Description = "eukhe daemon: sessions and the chat memory";
          Service = {
            ExecStart = "${lib.getExe cfg.package} --mode daemon";
            Restart = "on-failure";
          };
          Install.WantedBy = [ "default.target" ];
        };
  };
}
