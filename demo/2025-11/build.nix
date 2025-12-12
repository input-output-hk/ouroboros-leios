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
          packages = [ pkgs.process-compose ];
          inherit (config.devShells.dev-demo) IMMDB_SERVER CARDANO_NODE;
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
            # Non configurable
            WORKING_DIR = ".tmp-leios-202511-demo";
            UPSTREAM_NODE_PORT = 3001;
            NODE0_PORT = 3002;
            DOWNSTREAM_NODE_PORT = 3003;
            # Configurable (if you see DEF_FOO that's a default value for FOO if unset)
            DEF_CARDANO_NODE = config.devShells.dev-demo-2025-11.CARDANO_NODE;
            DEF_IMMDB_SERVER = config.devShells.dev-demo-2025-11.IMMDB_SERVER;
            DEF_REF_SLOT = 41;
            DEF_SECONDS_UNTIL_REF_SLOT = 5;
            DEF_LEIOS_MANIFEST = ./manifest.json;
            DEF_DATA_DIR = ./data;
            DEF_ANALYSE_PY = ./analyse.py;
            DEF_PYTHON3 = lib.getExe (
              pkgs.python3.withPackages (
                ps: with ps; [
                  pandas
                  matplotlib
                ]
              )
            );
          };
          text = ''
            process-compose --no-server -f ${./process-compose.yaml};
          '';
        };
        # TODO: drop this once we are sure no external uses exist anymore
        leios_202511_demo = demo-2025-11;
      };
    };
}
