{

  description = "TypeScript development environment for memory pool simulation.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;
          };
        };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            nodejs_24
            typescript
            vscode
          ];
          shellHook = ''
            export PATH="$PWD/node_modules/.bin:$PATH"
            export PS1="\[\e[1;32m\][nix-shell:\w]$\[\e[m\] "
            echo "Entering Nix shell with TypeScript tools . . . "
          '';
        };
      }
    );

}
