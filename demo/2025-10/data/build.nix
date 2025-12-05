{
  perSystem =
    { pkgs, ... }:
    {
      packages = {
        genesis = pkgs.stdenv.mkDerivation {
          name = "genesis";
          src = ./genesis;
          buildPhase = ''
            mkdir $out;
            cp * $out;
          '';
        };

        immutable-db = pkgs.stdenv.mkDerivation {
          name = "immutable-db";
          src = ./immdb-node/immutable;
          buildPhase = ''
            mkdir $out;
            cp * $out;
          '';
        };

      };
    };
}
