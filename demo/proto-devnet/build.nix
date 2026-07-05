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
      devShells.dev-demo-proto-devnet = pkgs.mkShell {
        name = "dev-demo-proto-devnet";
        src = ./.;
        inputsFrom = [
          config.devShells.dev-demo
          config.devShells.dev-demo-extras-x-ray
        ];
        packages = [
          pkgs.process-compose
          pkgs.sqlite
          pkgs.jq
          pkgs.yq
          pkgs.envsubst
          # tx-firehose: push-based N2C load generator targeting node1.
          inputs'.cardano-node-tx-firehose.packages.tx-firehose
          # Patched cardano-node + matching CLI from the
          # leios-prototype branch.
          inputs'.cardano-node-leios.packages.cardano-node
          inputs'.cardano-node-leios.packages.cardano-cli
        ];
        # To easily interact with node1 on the devnet from within the demo dir
        CARDANO_NODE_NETWORK_ID = 164;
        CARDANO_NODE_SOCKET_PATH = "tmp-devnet/node1/node.socket";
      };

      packages.demo-proto-devnet = pkgs.writeShellApplication {
        name = "leios-demo-proto-devnet";
        runtimeInputs =
          config.devShells.dev-demo-proto-devnet.nativeBuildInputs
          ++ config.devShells.dev-demo-proto-devnet.buildInputs
          ++ [ pkgs.sqlite ] # XXX: why is this not picked up from above?
          # XXX: Integration like this is a bit weird, but required if we want
          # to have the same environment overriding + process-compose
          # integration?
          ++ config.devShells.dev-demo-extras-x-ray.buildInputs;
        runtimeEnv = {
          # Override paths to point to nix store
          SOURCE_DIR = ./.;
          XRAY_SOURCE_DIR = ../extras/x-ray;
          GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
