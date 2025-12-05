# NOTE(bladyjoker): Removing the hydraJobs from iogx to produce it generically for the entire flake after
{ inputs, config, ... }:
{
  flake = builtins.removeAttrs (inputs.iogx.lib.mkFlake {

    inherit inputs;

    repoRoot = ./..;

    outputs = import ./outputs.nix;

    inherit (config) systems;
  }) [ "hydraJobs" ];
}
