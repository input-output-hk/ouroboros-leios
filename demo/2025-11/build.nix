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
        dev-demo-2025-11 = pkgs.mkShell {
          name = "dev-demo-2025-11";
          src = ./.;
          inputsFrom = [ config.devShells.dev-demo ];
          packages = [
            pkgs.process-compose
            pkgs.iproute2
            pkgs.sqlite
            config.packages.ss_http_exporter
          ];
          inherit (config.devShells.dev-demo) IMMDB_SERVER CARDANO_NODE;
        };
      };

      packages = lib.optionalAttrs (system == "x86_64-linux") rec {
        demo-2025-11 = pkgs.writeShellApplication {
          name = "leios_202511_demo";
          runtimeInputs =
            config.devShells.dev-demo-2025-11.nativeBuildInputs
            ++ config.devShells.dev-demo-2025-11.buildInputs
            ++ [ pkgs.sqlite ];
          runtimeEnv = {
            # Non configurable
            WORKING_DIR = ".tmp-leios-202511-demo";
            SCRIPTS=./scripts;
            PORT_UPSTREAM_NODE = 3001;
            PORT_NODE0 = 3002;
            PORT_DOWNSTREAM_NODE = 3003;
            IP_UPSTREAM_NODE="10.0.0.1";
            IP_NODE0="10.0.0.2";
            IP_DOWNSTREAM_NODE="10.0.0.3";
            # Configurable (if you see DEF_FOO that's a default value for FOO if unset)
            DEF_CARDANO_NODE = config.devShells.dev-demo-2025-11.CARDANO_NODE;
            DEF_IMMDB_SERVER = config.devShells.dev-demo-2025-11.IMMDB_SERVER;
            DEF_REF_SLOT = 41;
            DEF_SECONDS_UNTIL_REF_SLOT = 5;
            DEF_LEIOS_MANIFEST = ./manifest.json;
            DEF_DATA_DIR = ./data;
            DEF_ANALYSE_PY = ./analyse.py;
            DEF_PYTHON3 = lib.getExe (
              pkgs.python3.withPackages (
                ps: with ps; [
                  pandas
                  matplotlib
                ]
              )
            );
            DEF_RATE_UP_TO_N0="100Mbps";
            DEF_DELAY_UP_TO_N0="20ms";
            DEF_RATE_N0_TO_UP="100Mbps";
            DEF_DELAY_N0_TO_UP="20ms";
            DEF_RATE_N0_TO_DOWN="100Mbps";
            DEF_DELAY_N0_TO_DOWN="20ms";
            DEF_RATE_DOWN_TO_N0="100Mbps";
            DEF_DELAY_DOWN_TO_N0="20ms";
          };
          text = ''
            process-compose --no-server -f ${./process-compose.yaml};
          '';
        };
        # TODO: drop this once we are sure no external uses exist anymore
        leios_202511_demo = demo-2025-11;
      };
    };
}
