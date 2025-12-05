{ cardano-tracer, ... }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.cardano.tracer;
in
{

  imports = [
    ./simple-cardano-tracer/prometheus.nix
    ./simple-cardano-tracer/grafana.nix
    ./simple-cardano-tracer/loki.nix
  ];

  options.cardano.tracer = {
    enable = lib.mkEnableOption "Run cardano-tracer as service";

    config = lib.mkOption {
      type = lib.types.path;
      description = "Path to cardano-tracer config file";
    };

    package = lib.mkOption {
      type = lib.types.package;
      description = "cardano-tracer package to use";
      default = cardano-tracer;
    };

    minLogSeverity = lib.mkOption {
      type = lib.types.enum [
        "Debug"
        "Info"
        "Notice"
        "Warning"
        "Error"
        "Critical"
        "Alert"
        "Emergency"
      ];
      description = "Drop messages less severe than this";
      default = "Info";
    };

    address = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve on";
      default = "0.0.0.0";
    };

    port = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve on";
      default = 8888;
    };

    prometheusAddress = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve Prometheus on";
      default = "0.0.0.0";
    };

    prometheusPort = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve Prometheus on";
      default = 3000;
    };

    grafanaAddress = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve Grafana on";
      default = "0.0.0.0";
    };

    grafanaPort = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve Grafana on";
      default = 3001;
    };

    prometheusHttpSdAddress = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve Prometheus HTTP SD on";
      default = "0.0.0.0";
    };

    prometheusHttpSdPort = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve Prometheus HTTP SD on";
      default = 3002;
    };

    user = lib.mkOption {
      type = lib.types.str;
      default = "cardano-tracer";
      description = "User to run cardano-tracer service as";
    };

    group = lib.mkOption {
      type = lib.types.str;
      default = "cardano-tracer";
      description = "Group to run cardano-tracer service as";
    };
  };

  config = lib.mkIf cfg.enable {
    networking.firewall.allowedTCPPorts = [
      cfg.port
      cfg.prometheusPort
      cfg.prometheusHttpSdPort
      cfg.grafanaPort
      12345
    ];

    users = {
      users = {
        ${cfg.user} = {
          description = "User to run cardano-tracer service";
          inherit (cfg) group;
          createHome = false;
          isSystemUser = true;
        };
      };

      groups = {
        ${cfg.group} = {
          members = [ cfg.user ];
        };
      };
    };

    environment.etc = {
      "cardano-tracer/config.json" = {
        inherit (cfg) user group;
        source = cfg.config;
        mode = "0600"; # NOTE: We're patching this file in `preStart`
      };
    };

    systemd.services.cardano-tracer = {
      enable = true;
      after = [ "network.target" ];
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        Restart = "on-failure";
        RemainAfterExit = true;
        User = cfg.user;
        Group = cfg.group;
        ConfigurationDirectory = [ "cardano-tracer" ];
        StateDirectory = [ "cardano-tracer" ];
        RuntimeDirectory = [ "cardano-tracer" ];
      };

      path = [
        cfg.package
        pkgs.jq
        pkgs.socat
      ];

      preStart = ''
        cat ${cfg.config} \
           | jq ".network.contents = \"$RUNTIME_DIRECTORY/forwarder.sock\"" \
           | jq ".hasPrometheus.epHost = \"${cfg.prometheusAddress}"\" \
           | jq ".hasPrometheus.epPort = ${builtins.toString cfg.prometheusPort}" \
           > "$CONFIGURATION_DIRECTORY/config.json"
      '';

      script = ''
        cardano-tracer --config "$CONFIGURATION_DIRECTORY/config.json" \
             --state-dir "$STATE_DIRECTORY" \
             --min-log-severity "${cfg.minLogSeverity}"
      '';

      postStart = ''
        SOCKET="$RUNTIME_DIRECTORY/forwarder.sock"
        while [ ! -S "$SOCKET" ]; do
            echo "$SOCKET not found, sleeping for 1 seconds..."
            sleep 1
        done
        socat TCP4-LISTEN:${builtins.toString cfg.port},fork,reuseaddr UNIX-CONNECT:"$SOCKET" &
      '';

    };

  };

}
