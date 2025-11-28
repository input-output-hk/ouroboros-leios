{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  packages = [
    pkgs.nodejs
    pkgs.nodePackages.prettier
    pkgs.typescript
    pkgs.typescript-language-server
  ];
}
