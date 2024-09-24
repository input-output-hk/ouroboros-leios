{
  description = "Ouroboros Leios";


  inputs = {
    iogx = {
      url = "github:input-output-hk/iogx";
    };

    # Agda version 2.6.4.3
    agda-nixpkgs.url = "github:NixOS/nixpkgs?ref=4284c2b73c8bce4b46a6adf23e16d9e2ec8da4bb";

  };


  outputs = inputs: inputs.iogx.lib.mkFlake {

    inherit inputs;

    repoRoot = ./.;

    outputs = import ./nix/outputs.nix;

    # systems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" "aarch64-linux" ];

    # debug = false;

    # nixpkgsArgs = {
    #   config = {};
    #   overlays = [];
    # };

    # flake = { repoRoot, inputs }: {};
  };


  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };
}
