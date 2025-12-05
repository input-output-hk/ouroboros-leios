# Repo-wide Nixpkgs with different overlays
{ inputs, ... }:
{
  perSystem =
    { system, ... }:
    {

      _module.args = {
        pkgs = import inputs.nixpkgs {
          inherit system;
        };

      };
    };
}
