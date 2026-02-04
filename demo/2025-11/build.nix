{
  perSystem =
    {
      pkgs,
      config,
      lib,
      system,
      ...
    }:
    {
      devShells = lib.optionalAttrs (system == "x86_64-linux") {
        dev-demo-2025-11 = pkgs.mkShell {
          name = "dev-demo-2025-11";
          src = ./.;
          inputsFrom = [ config.devShells.dev-demo ];
          packages = [
            pkgs.process-compose
            pkgs.iproute2
            pkgs.sqlite
            pkgs.jq
            config.packages.ss_http_exporter
            (pkgs.python3.withPackages (
              ps: with ps; [
                pandas
                matplotlib
              ]
            ))
          ];
        };
      };

      packages = lib.optionalAttrs (system == "x86_64-linux") rec {
        demo-2025-11 = pkgs.writeShellApplication {
          name = "leios_202511_demo";
          runtimeInputs =
            config.devShells.dev-demo-2025-11.nativeBuildInputs
            ++ config.devShells.dev-demo-2025-11.buildInputs
            ++ [ pkgs.sqlite ];
          runtimeEnv = {
            # Override paths to point to nix store
            SOURCE_DIR = ./.;
            DATA_DIR = ./data;
            LEIOS_MANIFEST = ./manifest.json;
            CLUSTER_RUN = ./data/2025-10-10-13-29-24641-1050-50-blocks-50-coay-sup;
            # Nix-specific defaults (slower network simulation)
            RATE_UP_TO_N0 = "10Mbps";
            DELAY_UP_TO_N0 = "200ms";
            RATE_N0_TO_UP = "10Mbps";
            DELAY_N0_TO_UP = "200ms";
            RATE_N0_TO_DOWN = "10Mbps";
            DELAY_N0_TO_DOWN = "200ms";
            RATE_DOWN_TO_N0 = "10Mbps";
            DELAY_DOWN_TO_N0 = "200ms";
            SECONDS_UNTIL_REF_SLOT = "10";
            REF_SLOT = "11";
          };
          text = builtins.readFile ./run.sh;
        };
        # TODO: drop this once we are sure no external uses exist anymore
        leios_202511_demo = demo-2025-11;
      };
    };
}
