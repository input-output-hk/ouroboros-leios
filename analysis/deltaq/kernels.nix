{pkgs, ...}:

{

  kernel.python.minimal = {
    enable = true;
  };

  kernel.haskell.deltaq = {
    enable = true;
    nixpkgs = pkgs;
    haskellCompiler = "ghc94";
    extraHaskellPackages = p: with p; [

      # Required for charts in iHaskell kernel
      ihaskell
      ihaskell-charts
      Chart-cairo

      # Packages
      deltaq
      probability-polynomial

      # Library dependencies
      Chart
      exact-combinatorics
      graphviz
      lattices

      # Test dependencies, not strictly needed but perhaps convenient
      hspec
      hspec-discover
      QuickCheck
 
      # Benchmark dependencies, not strictly needed but perhaps convenient
      cassava
      criterion
      hvega
      optparse-applicative
      statistics
      vector

    ];
  };

}
