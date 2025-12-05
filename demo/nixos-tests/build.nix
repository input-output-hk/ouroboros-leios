{ inputs, config, ... }:
{
  perSystem =
    { pkgs, ... }:
    {
      packages.leios-demo-nixos-test = pkgs.testers.nixosTest (
        import ./test.nix {
          inherit inputs pkgs;
          outputs = config.flake;
        }
      );
    };
}
