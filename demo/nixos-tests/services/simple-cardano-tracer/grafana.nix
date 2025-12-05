{
  config,
  ...
}:
let
  cfg = config.cardano.tracer;
in
{
  services.alloy = {
    enable = true;
    extraFlags = [
      "--server.http.listen-addr=0.0.0.0:12345"
    ];
    configPath = ./grafana.alloy;
  };

  services.grafana = {
    enable = true;
    openFirewall = true;
    settings = {
      users.allow_sign_up = false;
      "auth.anonymous" = {
        enabled = true;
      };
      server = {
        http_addr = cfg.grafanaAddress;
        http_port = cfg.grafanaPort;
        enforce_domain = true;
        enable_gzip = true;
        domain = "localhost";
      };
    };

    provision = {
      enable = true;

      dashboards.settings.providers = [
        {
          name = "Some dashboards";
          disableDeletion = true;
          options = {
            path = "/etc/grafana-dashboards";
            foldersFromFilesStructure = true;
          };
        }
      ];

      datasources.settings.datasources = [
        {
          name = "Prometheus";
          type = "prometheus";
          url = "http://localhost:9001";
          isDefault = true;
          editable = false;
        }
        {
          name = "Loki";
          type = "loki";
          access = "proxy";
          url = "http://127.0.0.1:3100";
        }

      ];
    };
  };

  environment.etc = {
    "grafana-dashboards/empty-dashboard.json".source = ./empty-dashboard.json;
    "grafana-dashboards/cardano-node-dashboard.json".source = ./cardano-node-dashboard.json;
  };
}
