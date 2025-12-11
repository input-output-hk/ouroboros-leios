{

  perSystem =
    {
      pkgs,
      config,
      ...
    }:
    {

      devShells.dev-demo-extras-x-ray = pkgs.mkShell {
        packages = [
          pkgs.nettools
          pkgs.netcat
          pkgs.grafana
          pkgs.grafana-alloy
          pkgs.grafana-loki
          pkgs.prometheus
          pkgs.process-compose
          config.packages.ss_http_exporter
        ];
        GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        shellHook = '''';
      };

      packages.x_ray = pkgs.writeShellApplication {
        name = "x_ray";
        runtimeInputs = config.devShells.dev-demo-extras-x-ray.nativeBuildInputs;
        runtimeEnv = {
          inherit (config.devShells.dev-demo-extras-x-ray) GRAFANA_SHARE;
          GRAFANA_INI = ./grafana.ini;
          GRAFANA_HOMEPATH = ./grafana;
          ALLOY_CONFIG = ./alloy;
          PROMETHEUS_CONFIG = ./prometheus.yaml;
          LOKI_CONFIG = ./loki.yaml;
        };
        text = ''
          process-compose --no-server -f ${./process-compose.yaml};
        '';
      };

    };
}
