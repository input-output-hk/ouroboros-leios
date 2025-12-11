{
  pkgs ? import <nixpkgs> { },
}:

pkgs.mkShell {
  packages = with pkgs; [
    nixfmt-rfc-style
    nodejs
    nodePackages.prettier
    typescript
    typescript-language-server
  ];
}
