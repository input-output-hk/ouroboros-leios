let
  pkgs = import <nixpkgs> { };
  compiler = pkgs.haskell.packages.ghc96;
in
   compiler.developPackage {
    root = ./.;
    modifier = drv:
      pkgs.haskell.lib.addBuildTools drv (with pkgs.haskellPackages;
        [ cabal-install
          compiler.haskell-language-server
          stylish-haskell
          hlint
        ]);
  }