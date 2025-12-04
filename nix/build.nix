{inputs, ...}: {
  flake = inputs.iogx.lib.mkFlake {

    inherit inputs;

    repoRoot = ./..;

    outputs = import ./outputs.nix;

    systems = [ "x86_64-linux" ];
  };
}
