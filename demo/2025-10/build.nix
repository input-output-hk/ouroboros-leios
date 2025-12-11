{
  perSystem =
    {
      pkgs,
      inputs',
      lib,
      system,
      ...
    }:
    {
      packages = lib.optionalAttrs (system == "x86_64-linux") {
        leios-empty-db = pkgs.stdenv.mkDerivation {
          name = "leios-empty-db";
          src = ./.;
          buildInputs = [ pkgs.sqlite ];
          buildPhase = ''
            cat ${./leios-schema.sql} | sqlite3 $out;
          '';
        };

        leios-busy-db = pkgs.stdenv.mkDerivation {
          src = ./.;
          name = "leios-busy-db";
          buildInputs = [
            (inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus.getComponent "exe:leiosdemo202510")
            pkgs.jq
          ];
          outputs = [
            "out"
            "schedule"
          ];
          buildPhase = ''
            leiosdemo202510 generate leios.db ${./manifest.json} base-schedule.json

            # Make a schedule.json from the base-schedule.json such that the first number in each array is 182.9
            jq 'map(.[0] = 182.9)' base-schedule.json > schedule.json

            mv leios.db $out
            mv schedule.json $schedule
          '';
        };

        leios-202510-demo = pkgs.writeShellApplication {
          name = "leios-202510-demo";

          runtimeInputs = [
            inputs'.cardano-node.packages.cardano-node
            (inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus-cardano.getComponent "exe:immdb-server")
            (inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus-cardano.getComponent "exe:db-analyser")
            (inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus.getComponent "exe:leiosdemo202510")
            pkgs.toxiproxy
            pkgs.sqlite
            pkgs.jq
            pkgs.procps
            pkgs.coreutils
            pkgs.gnused
            pkgs.gnugrep
            (pkgs.python3.withPackages (
              ps: with ps; [
                pandas
                matplotlib
              ]
            ))
          ];

          text = ''
            # Set default values for required environment variables
            export SECONDS_UNTIL_REF_SLOT=''${SECONDS_UNTIL_REF_SLOT:-5}
            export REF_SLOT=''${REF_SLOT:-41}
            export CARDANO_NODE="${pkgs.lib.getExe inputs'.cardano-node.packages.cardano-node}"
            export IMMDB_SERVER="${pkgs.lib.getExe (inputs'.ouroboros-consensus.legacyPackages.hsPkgs.ouroboros-consensus-cardano.getComponent "exe:immdb-server")}"

            # Copy demo files to a temporary directory
            DEMO_DIR=$(mktemp -d)
            trap 'rm -rf "$DEMO_DIR"' EXIT

            cp ${./run-demo.sh} "$DEMO_DIR/run-demo.sh"
            cp ${./analyse.py} "$DEMO_DIR/analyse.py"
            cp ${./leios-schema.sql} "$DEMO_DIR/leios-schema.sql"
            cp ${./manifest.json} "$DEMO_DIR/manifest.json"

            # Copy cluster data to writable location
            cp -r ${./data} "$DEMO_DIR/data"
            chmod -R u+w "$DEMO_DIR/data"
            tar -xzf "$DEMO_DIR/data/immdb-node/immutable.tar.gz" -C "$DEMO_DIR/data/immdb-node/";
            export DATA="$DEMO_DIR/data"

            chmod +x "$DEMO_DIR/run-demo.sh"

            cd "$DEMO_DIR"
            exec ./run-demo.sh "$@"
          '';
        };
      };
    };
}
