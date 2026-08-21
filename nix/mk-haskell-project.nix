# Helper for declaring a per-cluster haskell.nix project with the shared
# defaults (CHaP repo, GHC version, no Hoogle in the haskell.nix shell).
# Returns:
#   * flake: the cabalProject's `flake { }` output, suitable for binding to
#       `legacyPackages.<cluster>`.
#   * hpkgs: the matching nixpkgs haskell.packages.<name> attrset, useful
#       for plain-mkShell dev shells (GHC, HLS, fourmolu). The version line
#       lives only here.
{ inputs, system }:
{
  name,
  src,
  cabalProjectFileName ? "cabal.project",
  compiler-nix-name ? "ghc9103",
}:
let
  hnPkgs = import ./haskell-nix-pkgs.nix { inherit inputs system; };
  project = hnPkgs.haskell-nix.cabalProject' {
    inherit
      name
      src
      cabalProjectFileName
      compiler-nix-name
      ;
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.CHaP;
    };
    shell.withHoogle = false;
  };
  # Map haskell.nix's compiler-nix-name (e.g. "ghc9103") to nixpkgs'
  # haskell.packages attribute (e.g. "ghc910") by dropping the trailing
  # patch digit.
  nixpkgsCompilerName = builtins.substring 0 (
    builtins.stringLength compiler-nix-name - 1
  ) compiler-nix-name;
in
{
  flake = project.flake { };
  hpkgs = (import inputs.nixpkgs { inherit system; }).haskell.packages.${nixpkgsCompilerName};
}
