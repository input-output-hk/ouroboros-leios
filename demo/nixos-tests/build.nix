{ inputs, config, ... }:
{
  perSystem =
    { pkgs, lib, ... }:
    {
      packages = lib.optionalAttrs pkgs.stdenv.isLinux {
        leios-demo-nixos-test = pkgs.testers.nixosTest (
          import ./test.nix {
            inherit inputs pkgs;
            outputs = config.flake;
          }
        );
      };
    };
}
