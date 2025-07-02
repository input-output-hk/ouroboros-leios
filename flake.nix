{
  description = "Ouroboros Leios";


  inputs = {
    iogx = {
      url = "github:input-output-hk/iogx";
    };

      leios-spec.url = "github:input-output-hk/ouroboros-leios-formal-spec?rev=86c5d8b8ccf3b16e279bd71efa26fb69000d8416";
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
