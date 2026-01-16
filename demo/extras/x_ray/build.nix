{

  perSystem =
    {
      pkgs,
      config,
      lib,
      system,
      ...
    }:
    {

      devShells = lib.optionalAttrs (system == "x86_64-linux") {
        dev-demo-extras-x-ray = pkgs.mkShell {
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
      };

      packages = lib.optionalAttrs (system == "x86_64-linux") rec {
        x-ray = pkgs.writeShellApplication {
          name = "x_ray";
          runtimeInputs = config.devShells.dev-demo-extras-x-ray.nativeBuildInputs;
          runtimeEnv = {
            GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
            GRAFANA_INI = ./grafana.ini;
            GRAFANA_HOMEPATH = ./grafana;
            ALLOY_CONFIG = ./alloy;
            PROMETHEUS_CONFIG = ./prometheus.yaml;
            LOKI_CONFIG = ./loki.yaml;
            LOG_PATH = "../../leios-202511-demo/.tmp-leios-202511-demo/*/log";
          };
          text = builtins.readFile ./run.sh;
        };
        # XXX: Drop once people forgot about it
        x_ray = x-ray;
      };
    };
}
