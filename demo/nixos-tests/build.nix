{ inputs, config, ... }:
{
  perSystem =
    {
      pkgs,
      lib,
      system,
      ...
    }:
    {
      packages = lib.optionalAttrs (system == "x86_64-linux") {
        leios-demo-nixos-test = pkgs.testers.nixosTest (
          import ./test.nix {
            inherit inputs pkgs;
            outputs = config.flake;
          }
        );
      };
    };
}
