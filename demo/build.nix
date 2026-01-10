{ inputs, lib, ... }:
{

  perSystem =
    {
      config,
      pkgs,
      inputs',
      system,
      ...
    }:
    {
      packages = lib.optionalAttrs (system == "x86_64-linux") (
        {
          leios-cardano-node = inputs'.cardano-node.packages.cardano-node;
        }
        // (with inputs'.ouroboros-consensus.legacyPackages.hsPkgs; {
          leios-immdb-server = ouroboros-consensus-cardano.components.exes.immdb-server;
          leios-demo-tool = ouroboros-consensus.components.exes.leiosdemo202510;
        })
        // rec {
          generate-leios-db = pkgs.writeShellApplication {
            name = "generate-leios-db";
            runtimeInputs =
              config.devShells.dev-demo.nativeBuildInputs ++ config.devShells.dev-demo.buildInputs ++ [ pkgs.jq ];
            text = ''
              # Set default manifest to the one packaged with this demo
              DEFAULT_MANIFEST="${./manifest.json}"
              ${builtins.readFile ./scripts/generate-leios-db.sh}
            '';
          };

          leios-demo = pkgs.writeShellApplication {
            name = "leios-demo";
            runtimeInputs =
              config.devShells.dev-demo.nativeBuildInputs
              ++ config.devShells.dev-demo.buildInputs
              ++ [
                pkgs.iproute2
                pkgs.sqlite
              ];
            runtimeEnv = {
              # Non configurable
              WORKING_DIR = ".tmp-leios-demo";
              SCRIPTS = ./scripts;
              PORT_UPSTREAM_NODE = 3001;
              PORT_NODE0 = 3002;
              PORT_DOWNSTREAM_NODE = 3003;
              IP_UPSTREAM_NODE = "10.0.0.1";
              IP_NODE0 = "10.0.0.2";
              IP_DOWNSTREAM_NODE = "10.0.0.3";
              # Configurable (if you see DEF_FOO that's a default value for FOO if unset)
              DEF_CARDANO_NODE = config.devShells.dev-demo.CARDANO_NODE;
              DEF_IMMDB_SERVER = config.devShells.dev-demo.IMMDB_SERVER;
              DEF_SS_HTTP_EXPORTER = config.devShells.dev-demo.SS_HTTP_EXPORTER;
              DEF_LEIOS_MANIFEST = ./manifest.json;
              DEF_DATA_DIR = ./data;
              DEF_ANALYSE = ./analyse.py;
              DEF_PYTHON3 = lib.getExe (
                pkgs.python3.withPackages (
                  ps: with ps; [
                    pandas
                    matplotlib
                  ]
                )
              );
              DEF_RATE_UP_TO_N0 = "10Mbps";
              DEF_DELAY_UP_TO_N0 = "200ms";
              DEF_RATE_N0_TO_UP = "10Mbps";
              DEF_DELAY_N0_TO_UP = "200ms";
              DEF_RATE_N0_TO_DOWN = "10Mbps";
              DEF_DELAY_N0_TO_DOWN = "200ms";
              DEF_RATE_DOWN_TO_N0 = "10Mbps";
              DEF_DELAY_DOWN_TO_N0 = "200ms";

              # Time until the ref slot is reached and Leios traffic starts
              DEF_SECONDS_UNTIL_REF_SLOT = 10;
              # NOTE This depends marks the start of the Leios traffic and depends
              # on the praos schedule in the CLUSTER_RUN
              DEF_REF_SLOT = 11; # first block in data
              DEF_CLUSTER_RUN = ./data/2025-10-10-13-29-24641-1050-50-blocks-50-coay-sup;
              # DEF_CLUSTER_RUN = ./data/2025-10-08-19-42-9d25e-1050-50-blocks-50-coay-sup;
            };
            text = ''
              process-compose --no-server -f ${./process-compose.yaml};
            '';
          };
        }
      );

      checks = {
        pre-commit-demo = inputs.pre-commit-hooks.lib.${system}.run {
          src = ./.;
          hooks = import ./pre-commit-hooks.nix;
        };
      };

      devShells = lib.optionalAttrs (system == "x86_64-linux") {
        dev-demo = pkgs.mkShell {
          name = "dev-demo";
          src = ./.;

          buildInputs =
            config.checks.pre-commit-demo.enabledPackages
            ++ [
              inputs'.cardano-node.packages.cardano-node
              inputs'.cardano-node.packages.cardano-tracer
            ]
            ++ (with inputs'.ouroboros-consensus.legacyPackages.hsPkgs; [
              ouroboros-consensus-cardano.components.exes.immdb-server
              ouroboros-consensus-cardano.components.exes.db-analyser
              ouroboros-consensus-cardano.components.exes.db-immutaliser
              ouroboros-consensus.components.exes.leiosdemo202510
            ])
            ++ (with pkgs.python3Packages; [

              python
              ipython
              pandas
              altair
              pip
              virtualenv
              python-lsp-server
              black
              itables
              ipywidgets
              jupyterlab-widgets
              widgetsnbextension
              jupyterlab
              jupyter
              plotly
              matplotlib

            ])
            ++ [
              pkgs.fd
              pkgs.bash
              pkgs.toxiproxy
              pkgs.sqlite
              pkgs.grafana-alloy
              pkgs.loki
              pkgs.iproute2 # ss
              pkgs.process-compose
              config.packages.ss_http_exporter
            ];

          CARDANO_NODE = pkgs.lib.getExe inputs'.cardano-node.packages.cardano-node;
          IMMDB_SERVER = pkgs.lib.getExe inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus-cardano.components.exes.immdb-server;
          SS_HTTP_EXPORTER = pkgs.lib.getExe config.packages.ss_http_exporter;
        };
      };

    };
}
