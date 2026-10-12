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
      type = lib.types.nullOr lib.types.package;
      default = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
      defaultText = lib.literalExpression "eukhe.packages.\${system}.default";
      description = ''
        The eukhe package (the pinned prebuilt release when one exists for the
        system, else built from source). `null` installs no package: another
        tool (mise, for example) provides `eukhe` on PATH.
      '';
    };

    settings = lib.mkOption {
      type = json.type;
      default = { };
      example = lib.literalExpression ''
        {
          memory = { model = "anthropic/claude-sonnet-5-5"; thinking = "medium"; };
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

    gateway = {
      enable = lib.mkEnableOption ''
        the Signal gateway (a systemd user service, `eukhe gateway`): chat with
        the CLI session from the Signal app. Run `eukhe gateway` once in a
        terminal to link the phone; the service starts after the link
      '';

      command = lib.mkOption {
        type = lib.types.str;
        default = lib.getExe cfg.package;
        defaultText = lib.literalExpression "lib.getExe programs.eukhe.package";
        example = "\${config.home.homeDirectory}/.local/share/mise/shims/eukhe";
        description = ''
          The eukhe executable the service runs. Set it when `package` is
          `null` (eukhe comes from mise, for example). The gateway starts the
          daemon from this executable when none runs.
        '';
      };

      signalCli = lib.mkPackageOption pkgs "signal-cli" { };

      path = lib.mkOption {
        type = lib.types.listOf lib.types.str;
        default = [ ];
        example = lib.literalExpression ''[ "''${config.home.homeDirectory}/.local/share/mise/shims" ]'';
        description = ''
          Directories added to the service PATH after signal-cli and the
          user profile. A daemon that the gateway starts inherits this PATH,
          and the agent's tools run with it.
        '';
      };
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [
      {
        assertion = !cfg.daemon.enable || cfg.package != null;
        message = "programs.eukhe.daemon.enable needs programs.eukhe.package.";
      }
      {
        assertion = !cfg.gateway.enable || pkgs.stdenv.hostPlatform.isLinux;
        message = "programs.eukhe.gateway.enable needs systemd (Linux).";
      }
    ];

    home.packages =
      lib.optional (cfg.package != null) cfg.package
      ++ lib.optional cfg.gateway.enable cfg.gateway.signalCli;

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

    # The service waits for the link: `eukhe gateway` in a terminal links the
    # phone and restarts it. KillMode=process keeps a daemon that the gateway
    # started alive across gateway restarts.
    systemd.user.services.eukhe-gateway = lib.mkIf cfg.gateway.enable {
      Unit = {
        Description = "eukhe Signal gateway";
        After = [ "network-online.target" ] ++ lib.optional cfg.daemon.enable "eukhe-daemon.service";
        Wants = lib.optional cfg.daemon.enable "eukhe-daemon.service";
        ConditionPathExists = "%h/.local/share/signal-cli/data/accounts.json";
      };
      Service = {
        ExecStart = "${cfg.gateway.command} gateway";
        Environment = [
          "PATH=${
            lib.concatStringsSep ":" (
              [
                "${cfg.gateway.signalCli}/bin"
                "${config.home.profileDirectory}/bin"
              ]
              ++ cfg.gateway.path
              ++ [
                "/run/wrappers/bin"
                "/run/current-system/sw/bin"
              ]
            )
          }"
        ];
        Restart = "always";
        RestartSec = 5;
        KillMode = "process";
      };
      Install.WantedBy = [ "default.target" ];
    };
  };
}
