{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    lean4
    elan
    vscode
  ];
  shellHook = ''
    echo "Entering Nix shell with Lean 4, Elan, and VS Code..."
  '';
}
