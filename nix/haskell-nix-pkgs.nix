# Returns a nixpkgs instance with the haskell.nix overlay applied,
# using haskell.nix's bundled (compatible) nixpkgs-unstable.
{ inputs, system }:
import inputs.haskell-nix.inputs.nixpkgs-unstable {
  inherit system;
  inherit (inputs.haskell-nix) config;
  overlays = [ inputs.haskell-nix.overlay ];
}
