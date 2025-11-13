{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  packages = [
    pkgs.nodePackages.prettier
    pkgs.typescript
    pkgs.typescript-language-server
  ];
}
