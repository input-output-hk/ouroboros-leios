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
          ];
          inherit (config.devShells.dev-demo) CARDANO_NODE;
          CARDANO_CLI = lib.getExe inputs'.cardano-node.packages.cardano-cli;
        };
      };

      packages.demo-proto-devnet = pkgs.writeShellApplication {
        name = "leios-demo-proto-devnet";
        runtimeInputs = config.devShells.dev-demo-proto-devnet.buildInputs;
        runtimeEnv = {
          inherit (config.devShells.dev-demo-proto-devnet) CARDANO_NODE CARDANO_CLI;
        };
        text = builtins.readFile ./start.bash;
      };
    };
}
