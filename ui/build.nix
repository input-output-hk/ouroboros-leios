{
  perSystem =
    { config, pkgs, ... }:
    let
      # NOTE: This requires the whole repository as context to resolve symlinks
      # properly. There is no easy way to restrict the derivation inputs
      # meaningfully so we need to accept invalidation of this on any change on
      # the repo (or enumerate all the symlinks here).
      resolvedSrc = pkgs.stdenv.mkDerivation {
        name = "leios-ui-source-resolved";
        src = ../.;
        buildCommand = ''
          mkdir -p $out
          cp -rL $src/ui/* $out/
          chmod -R u+w $out
          cp ${config.packages.geojson} $out/public/data/ne_110m_admin_0_countries.geojson
        '';
      };
    in
    rec {
      devShells.dev-ui = pkgs.mkShell {
        inherit (config.pre-commit.settings) shellHook;
        buildInputs = config.pre-commit.settings.enabledPackages;
        packages = with pkgs; [
          nodejs
          nodePackages.prettier
          typescript
          typescript-language-server
        ];
      };

      packages.geojson = pkgs.fetchurl {
        url = "https://raw.githubusercontent.com/nvkelso/natural-earth-vector/master/geojson/ne_110m_admin_0_countries.geojson";
        hash = "sha256-aGbId9Ocupw1diCHiDmzNtVp+MZi08+rTLHb4tOcl38=";
      };

      packages.ui = pkgs.buildNpmPackage {
        name = "leios-ui";
        src = resolvedSrc;

        npmDeps = pkgs.importNpmLock { npmRoot = ./.; };
        inherit (pkgs.importNpmLock) npmConfigHook;

        nativeBuildInputs = [ pkgs.curl ];

        buildPhase = ''
          npm run build
        '';

        installPhase = ''
          mkdir -p $out/visualizer/
          cp -r dist/* $out/visualizer/
        '';
      };

      packages.ui-live = pkgs.writeShellApplication {
        name = "leios-ui-live";
        runtimeInputs = [ pkgs.http-server ];
        text = ''
          if [[ -n "$1" ]]; then
             param="?scenario=$1"
          fi
          http-server ${packages.ui} -o /visualizer/"$param"
        '';
      };
    };
}
