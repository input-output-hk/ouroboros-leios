{
  pkgs ? import <nixpkgs> { },
}:

pkgs.mkShell {
  packages = with pkgs; [
    nodejs
    nodePackages.prettier
    typescript
    typescript-language-server
  ];
}
