{
  # Typos
  typos.enable = false;

  # Markdown
  markdownlint.enable = true;
  markdownlint.settings.configuration = builtins.fromJSON (builtins.readFile ./.markdownlint.json);

  # Nix
  nixfmt-rfc-style.enable = true;
  deadnix.enable = true;
  statix.enable = true;

  # Shell
  shellcheck.enable = true;
  shfmt.enable = true;
  shfmt.settings.simplify = false;

  # Python
  black.enable = true;
  ruff.enable = true;

  # Yaml
  yamllint.enable = true;
  yamllint.settings.configuration = ''
    extends: relaxed
    rules:
      line-length:
        max: 120
  '';
}
