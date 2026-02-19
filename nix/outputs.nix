{
  repoRoot,
  pkgs,
  lib,
  system,
  ...
}:

let

  inherit (repoRoot.nix) project agda;
  artifacts = import ./artifacts.nix { inherit pkgs; };

in

[
  (lib.optionalAttrs (system == "x86_64-linux") project.flake)
  {
    packages = agda // artifacts;
  }
]
