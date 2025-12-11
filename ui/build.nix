{
  perSystem =
    { pkgs, ... }:
    # Resolve symlinks
    let
      resolvedSrc = pkgs.stdenv.mkDerivation {
        name = "leios-ui-source-resolved";
        src = ../.;
        buildCommand = ''
          mkdir -p $out
          cp -rL $src/ui/* $out/
        '';
      };
    in
    {
      packages.ui = pkgs.buildNpmPackage {
        name = "leios-ui";
        src = resolvedSrc;

        npmDeps = pkgs.importNpmLock { npmRoot = ./.; };
        inherit (pkgs.importNpmLock) npmConfigHook;

        buildPhase = ''
          npm run build
        '';
        installPhase = ''
          mkdir -p $out
          cp -r dist/* $out/
        '';
      };
    };
}
