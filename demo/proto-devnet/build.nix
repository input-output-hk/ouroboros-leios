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
            pkgs.envsubst
            inputs'.cardano-node.packages.cardano-testnet
            inputs'.cardano-node.packages.cardano-cli
            # TODO: re-enable patched node inherit (config.devShells.dev-demo) CARDANO_NODE;
            inputs'.cardano-node.packages.cardano-node
            inputs'.cardano-node.packages.tx-generator
          ];
          # To easily interact with node1 on the devnet from within the demo dir
          CARDANO_NODE_NETWORK_ID = 164;
          CARDANO_NODE_SOCKET_PATH = "tmp-devnet/node1/node.socket";
        };
      };

      packages.demo-proto-devnet = pkgs.writeShellApplication {
        name = "leios-demo-proto-devnet";
        runtimeInputs =
          config.devShells.dev-demo-proto-devnet.nativeBuildInputs
          ++ config.devShells.dev-demo-proto-devnet.buildInputs
          ++ [ pkgs.sqlite ]; # XXX: why is this not picked up from above?
        runtimeEnv = {
          # Override paths to point to nix store
          SOURCE_DIR = ./.;
          LEIOS_SCHEMA = ../2025-11/data/leios-schema.sql;
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
