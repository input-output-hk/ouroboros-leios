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
            inputs'.cardano-node.packages.cardano-testnet
            inputs'.cardano-node.packages.cardano-cli
            inputs'.cardano-node.packages.tx-generator
          ];
          # inherit (config.devShells.dev-demo) CARDANO_NODE;
          CARDANO_NODE = lib.getExe inputs'.cardano-node.packages.cardano-node;
          CARDANO_CLI = lib.getExe inputs'.cardano-node.packages.cardano-cli;

          # To easily interact with node1 on the devnet from within the demo dir
          CARDANO_NODE_NETWORK_ID = 164;
          CARDANO_NODE_SOCKET_PATH = "./devnet/socket/node1/sock";
        };
      };

      packages.demo-proto-devnet = pkgs.writeShellApplication {
        name = "leios-demo-proto-devnet";
        runtimeInputs = config.devShells.dev-demo-proto-devnet.buildInputs;
        runtimeEnv = {
          inherit (config.devShells.dev-demo-proto-devnet) CARDANO_NODE CARDANO_CLI;
          SCRIPT_DIR = ./.; # FIXME: re-use 2025-11 sql file
        };
        text = builtins.readFile ./start.bash;
      };
    };
}
