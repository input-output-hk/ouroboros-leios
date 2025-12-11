{
  perSystem =
    { pkgs, ... }:
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
        '';
      };
    in
    rec {
      packages.ui = pkgs.buildNpmPackage {
        name = "leios-ui";
        src = resolvedSrc;

        npmDeps = pkgs.importNpmLock { npmRoot = ./.; };
        inherit (pkgs.importNpmLock) npmConfigHook;

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
          http-server ${packages.ui} -o /visualizer/?scenario=2
        '';
      };
    };
}
