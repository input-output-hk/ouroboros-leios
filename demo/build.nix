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
      packages =
        lib.optionalAttrs (system == "x86_64-linux") {
          leios-cardano-node = inputs'.cardano-node.packages.cardano-node;
        }
        // (with inputs'.ouroboros-consensus.legacyPackages.hsPkgs; {
          leios-immdb-server = ouroboros-consensus-cardano.getComponent "exe:immdb-server";
          leios-demo-tool = ouroboros-consensus.getComponent "exe:leiosdemo202510";
        });

      checks = {
        pre-commit-demo = inputs.pre-commit-hooks.lib.${system}.run {
          src = ./.;
          hooks = import ./pre-commit-hooks.nix;
        };
      };

      devShells = lib.optionalAttrs (system == "x86_64-linux") {
        dev-demo = pkgs.mkShell {
          name = "dev-demo";

          buildInputs =
            config.checks.pre-commit-demo.enabledPackages
            ++ [
              inputs'.cardano-node.packages.cardano-node
              inputs'.cardano-node.packages.cardano-tracer
            ]
            ++ (with inputs'.ouroboros-consensus.legacyPackages.hsPkgs; [
              (ouroboros-consensus-cardano.getComponent "exe:immdb-server")
              (ouroboros-consensus-cardano.getComponent "exe:db-analyser")
              (ouroboros-consensus.getComponent "exe:leiosdemo202510")
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
            ];

          CARDANO_NODE = pkgs.lib.getExe inputs'.cardano-node.packages.cardano-node;
          IMMDB_SERVER = pkgs.lib.getExe (
            inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus-cardano.getComponent "exe:immdb-server"
          );
        };
      };

    };
}
