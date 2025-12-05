# Sourced by build.nix
# https://github.com/cachix/git-hooks.nix?tab=readme-ov-file#hooks
{
  # Nix
  nixfmt-rfc-style.enable = true;
  deadnix.enable = true;
  statix.enable = true;

  # Haskell
  fourmolu.enable = true;
  hlint.enable = true;

  # Python
  black.enable = true;
  ruff.enable = true;
}
