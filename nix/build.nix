{ inputs, ... }:
{
  perSystem =
    {
      pkgs,
      system,
      lib,
      ...
    }:
    let
      agda = import ./agda.nix {
        inherit
          pkgs
          inputs
          system
          lib
          ;
      };
      artifacts = import ./artifacts.nix { inherit pkgs; };
    in
    {
      packages = agda // artifacts;
    };
}
