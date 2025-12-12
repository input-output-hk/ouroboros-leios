{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.prometheus.http-sd;
in
{

  imports = [
  ];

  options.prometheus.http-sd = {
    enable = lib.mkEnableOption "Run Prometheus HTTP Service Discovery as service";

    openFirewall = lib.mkEnableOption "Open the port in the firewall";

    address = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve on";
      default = "0.0.0.0";
    };

    port = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve on";
      default = 3002;
    };

    cardanoTracerPrometheusEndpoint = lib.mkOption {
      type = lib.types.str;
      description = "cardano-tracer Prometheus endpoint";
    };

    user = lib.mkOption {
      type = lib.types.str;
      default = "prometheus-http-sd";
      description = "User to run the service as";
    };

    group = lib.mkOption {
      type = lib.types.str;
      default = "prometheus-http-sd";
      description = "Group to run the service as";
    };

  };

  config =
    lib.mkIf cfg.openFirewall {
      networking.firewall.allowedTCPPorts = [ cfg.port ];
    }
    // lib.mkIf cfg.enable {
      users = {
        users = {
          ${cfg.user} = {
            description = "User to run prometheus-http-sd service";
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

      systemd.services.prometheus-http-sd = {
        enable = true;
        after = [ "network.target" ];
        wantedBy = [ "multi-user.target" ];
        serviceConfig = {
          Restart = "on-failure";
          RemainAfterExit = true;
          User = cfg.user;
          Group = cfg.group;
          ConfigurationDirectory = [ "prometheus-http-sd" ];
          StateDirectory = [ "prometheus-http-sd" ];
          RuntimeDirectory = [ "prometheus-http-sd" ];
        };

        path = [
          pkgs.jq
          pkgs.curl
          pkgs.busybox
          pkgs.socat
        ];

        script = ''
          CARDANO_TRACER_PROMETHEUS=${cfg.cardanoTracerPrometheusEndpoint} socat -d TCP4-LISTEN:${builtins.toString cfg.port},bind=${cfg.address},reuseaddr,fork SYSTEM:${./prometheus-http-sd.sh},sigint,nofork
        '';
      };

    };

}
