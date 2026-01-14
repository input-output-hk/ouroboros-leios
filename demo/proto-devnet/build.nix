{
  perSystem =
    {
      pkgs,
      config,
      lib,
      system,
      inputs',
      ...
    }:
    {
      devShells = lib.optionalAttrs (system == "x86_64-linux") {
        dev-demo-proto-devnet = pkgs.mkShell {
          name = "dev-demo-proto-devnet";
          src = ./.;
          inputsFrom = [ config.devShells.dev-demo ];
          packages = [
            pkgs.process-compose
            pkgs.sqlite
            pkgs.jq
            inputs'.cardano-node.packages.cardano-testnet
            inputs'.cardano-node.packages.cardano-cli
            inputs'.cardano-node.packages.tx-generator
          ];
          # TODO: re-enable patched node inherit (config.devShells.dev-demo) CARDANO_NODE;
          CARDANO_NODE = lib.getExe inputs'.cardano-node.packages.cardano-node;
          CARDANO_CLI = lib.getExe inputs'.cardano-node.packages.cardano-cli;

          # To easily interact with node1 on the devnet from within the demo dir
          CARDANO_NODE_NETWORK_ID = 164;
          CARDANO_NODE_SOCKET_PATH = "./devnet/node1/node.socket";
        };
      };

      packages.demo-proto-devnet = pkgs.writeShellApplication {
        name = "leios-demo-proto-devnet";
        runtimeInputs =
          config.devShells.dev-demo-proto-devnet.nativeBuildInputs
          ++ config.devShells.dev-demo-proto-devnet.buildInputs;
        runtimeEnv = {
          # Override paths to point to nix store
          SCRIPTS = ./scripts;
          CONFIG_DIR = ./config;
          LEIOS_SCHEMA = ../2025-11/data/leios-schema.sql;

          # Inherit cardano binaries from dev shell
          inherit (config.devShells.dev-demo-proto-devnet) CARDANO_NODE CARDANO_CLI;
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
