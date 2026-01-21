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
          shellHook = "";
        };
      };

      packages = lib.optionalAttrs (system == "x86_64-linux") rec {
        x-ray = pkgs.writeShellApplication {
          name = "x-ray";
          runtimeInputs = config.devShells.dev-demo-extras-x-ray.nativeBuildInputs;
          runtimeEnv = {
            SOURCE_DIR = ./.;
            GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
          };
          text = builtins.readFile ./run.sh;
        };
      };
    };
}
