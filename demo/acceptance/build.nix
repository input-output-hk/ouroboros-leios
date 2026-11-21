{
  perSystem =
    {
      pkgs,
      config,
      lib,
      system,
      ...
    }:
    lib.optionalAttrs (system == "x86_64-linux") {
      devShells.dev-demo-acceptance = pkgs.mkShell {
        name = "dev-demo-acceptance";
        inputsFrom = [ config.devShells.dev-demo-proto-devnet ];
        CARDANO_NODE_NETWORK_ID = 164;
        CARDANO_NODE_SOCKET_PATH = "tmp-acceptance/node2/node.socket";
      };

      packages.demo-acceptance = pkgs.writeShellApplication {
        name = "leios-demo-acceptance";
        runtimeInputs =
          config.devShells.dev-demo-acceptance.nativeBuildInputs
          ++ config.devShells.dev-demo-acceptance.buildInputs
          ++ [ pkgs.sqlite ]
          ++ config.devShells.dev-demo-extras-x-ray.buildInputs;
        runtimeEnv = {
          ACCEPTANCE_DIR = ./.;
          PROTO_DEVNET_DIR = ../proto-devnet;
          SOURCE_DIR = ../proto-devnet;
          XRAY_SOURCE_DIR = ../extras/x-ray;
          GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
