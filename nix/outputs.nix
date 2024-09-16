{ repoRoot, inputs, pkgs, lib, system }:

let

  project = repoRoot.nix.project;
  agda = import ./agda.nix {inherit pkgs lib inputs;};

in

[
  (project.flake)
  {
    packages.leiosSpec = agda.leiosSpec;
  }
]
