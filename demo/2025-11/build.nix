{
  perSystem =
    {
      pkgs,
      config,
      lib,
      ...
    }:
    {
      devShells.dev-leios-202511-demo = pkgs.mkShell {
        name = "dev-leios-202511-demo";
        src = ./.;
        inputsFrom = [ config.devShells.dev-demo ];
        packages = [ pkgs.process-compose ];
        inherit (config.devShells.dev-demo) IMMDB_SERVER CARDANO_NODE;
      };

      packages = {
        leios_202511_demo = pkgs.writeShellApplication {
          name = "leios_202511_demo";
          runtimeInputs =
            config.devShells.dev-leios-202511-demo.nativeBuildInputs
            ++ config.devShells.dev-leios-202511-demo.buildInputs;
          runtimeEnv = {
            # Non configurable
            WORKING_DIR = ".tmp-leios-202511-demo";
            UPSTREAM_NODE_PORT = 3001;
            NODE0_PORT = 3002;
            DOWNSTREAM_NODE_PORT = 3003;
            # Configurable (if you see DEF_FOO that's a default value for FOO if unset)
            DEF_CARDANO_NODE = config.devShells.dev-leios-202511-demo.CARDANO_NODE;
            DEF_IMMDB_SERVER = config.devShells.dev-leios-202511-demo.IMMDB_SERVER;
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
      };
    };
}
