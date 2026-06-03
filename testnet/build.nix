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
    lib.optionalAttrs (system == "x86_64-linux") {
      devShells.dev-testnet = pkgs.mkShell {
        name = "dev-testnet";
        src = ./.;
        inputsFrom = [
          config.devShells.dev-demo-extras-x-ray
        ];
        packages = [
          # Patched cardano-node with the Leios-prototype consensus +
          # ledger pinned via the cardano-node-leios flake input.
          inputs'.cardano-node-leios.packages.cardano-node
          # CLI to query the local node socket (e.g. tip catchup checks).
          inputs'.cardano-node.packages.cardano-cli
          pkgs.process-compose
          pkgs.envsubst
          pkgs.bash
          pkgs.coreutils
          pkgs.curl
          pkgs.jq
        ];

        # Convenient defaults for `cardano-cli query ...` against the
        # local testnet relay's socket.
        CARDANO_NODE_NETWORK_ID = 164;
        CARDANO_NODE_SOCKET_PATH = "tmp-testnet/node.socket";
      };

      packages.leios-testnet-relay = pkgs.writeShellApplication {
        name = "leios-testnet-relay";
        runtimeInputs =
          config.devShells.dev-testnet.nativeBuildInputs
          ++ config.devShells.dev-testnet.buildInputs
          # XXX: Integration like this is a bit weird, but required if we want
          # to have the same environment overriding + process-compose
          # integration (see demo/proto-devnet/build.nix).
          ++ config.devShells.dev-demo-extras-x-ray.buildInputs;
        runtimeEnv = {
          SOURCE_DIR = ./.;
          XRAY_SOURCE_DIR = ../demo/extras/x-ray;
          GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
