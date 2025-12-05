{
  config,
  ...
}:
let
  cfg = config.cardano.tracer;
in
{
  imports = [
    ./prometheus-http-sd.nix
  ];

  prometheus.http-sd = {
    enable = true;
    openFirewall = true;
    address = cfg.prometheusHttpSdAddress;
    port = cfg.prometheusHttpSdPort;
    cardanoTracerPrometheusEndpoint = "localhost:${builtins.toString cfg.prometheusPort}";
  };

  services.prometheus = {
    enable = true;
    port = 9001;

    exporters = {
      node = {
        enable = true;
        enabledCollectors = [
          "tcpstat"
          "qdisc"
        ];
        port = 9002;
      };
    };

    scrapeConfigs = [
      {
        job_name = "node-exporter";
        static_configs = [
          {
            targets = [ "127.0.0.1:9002" ];
          }
        ];
      }
      {
        job_name = "alloy";
        static_configs = [
          {
            targets = [ "127.0.0.1:12345" ];
          }
        ];
      }
      {
        job_name = "cardano-tracer";

        http_sd_configs = [
          {
            url = "http://localhost:${builtins.toString cfg.prometheusHttpSdPort}/";
            refresh_interval = "3s";
          }
        ];

        relabel_configs = [
          {
            source_labels = [ "__metrics_path__" ];
            target_label = "__metrics_path__";
          }
        ];
      }
    ];
  };
}
