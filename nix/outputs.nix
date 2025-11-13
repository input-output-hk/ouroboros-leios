{ repoRoot, inputs, pkgs, lib, system }:

let

  project = repoRoot.nix.project;
  agda = import ./agda.nix { inherit pkgs lib inputs; };
  artifacts = import ./artifacts.nix { inherit pkgs; };

in

[
  (project.flake)
  {
    packages = agda // artifacts;

    devShells.docs = pkgs.mkShell {
      packages = [
        # To format *.md files
        pkgs.nodePackages.prettier
      ];
    };

    devShells.ui = import ../ui/shell.nix { inherit pkgs; };
  }
]
