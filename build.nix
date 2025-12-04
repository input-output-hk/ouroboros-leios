{

  perSystem =
    {
      config,
      pkgs,
      inputs',
      ...
    }:
    {
      devShells.dev-top-level = pkgs.mkShell {
        name = "dev-top-level";

        inherit (config.pre-commit.settings) shellHook;

        buildInputs = config.pre-commit.settings.enabledPackages;
      };

      formatter = pkgs.writeShellScriptBin "pre-commit-run" ''
        ${pkgs.lib.getExe config.pre-commit.settings.package} run --all-files --config ${config.pre-commit.settings.configFile}
      '';

      pre-commit.settings = {
        hooks = import ./pre-commit-hooks.nix;
      };

    };
}
