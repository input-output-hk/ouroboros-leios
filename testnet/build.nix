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
    lib.optionalAttrs (system == "x86_64-linux") (
      let
        # One dev-testnet shell per Leios EB Plutus budget factor. The
        # cardano-node-eb<n>x packages are built with the EB ExUnits budget
        # set to <n> times the RB budget (see the cardano-node-leios input's
        # flake variants); the plain cardano-node package is the 1x baseline.
        mkTestnetShell = shellName: nodePackage:
          pkgs.mkShell {
            name = shellName;
            src = ./.;
            inputsFrom = [
              config.devShells.dev-demo-extras-x-ray
            ];
            packages = [
              # Patched cardano-node with the Leios-prototype consensus +
              # ledger pinned via the cardano-node-leios flake input.
              inputs'.cardano-node-leios.packages.${nodePackage}
              # CLI to query the local node socket (e.g. tip catchup checks).
              inputs'.cardano-node-leios.packages.cardano-cli
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
      in
      {
        devShells = {
          # Default dev-testnet shell: EB Plutus budget = 4x the RB budget.
          dev-testnet = mkTestnetShell "dev-testnet" "cardano-node-eb4x";
          dev-testnet-eb1x = mkTestnetShell "dev-testnet-eb1x" "cardano-node";
          dev-testnet-eb2x = mkTestnetShell "dev-testnet-eb2x" "cardano-node-eb2x";
          dev-testnet-eb8x = mkTestnetShell "dev-testnet-eb8x" "cardano-node-eb8x";
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
          # Reuse the proto-devnet dashboards until we ship testnet-specific ones.
          DEMO_DASHBOARDS_DIR = ../demo/proto-devnet/config/dashboards;
          GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        };
        text = builtins.readFile ./run.sh;
      };
    }
    );
}
