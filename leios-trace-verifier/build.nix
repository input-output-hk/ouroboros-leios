{ inputs, ... }:
{
  perSystem =
    {
      config,
      pkgs,
      system,
      ...
    }:
    let
      inherit (pkgs) lib;
      hpkgs = pkgs.haskell.packages.ghc910;
      agda = import ../nix/agda.nix {
        inherit
          pkgs
          inputs
          system
          lib
          ;
      };

      hnPkgs = import ../nix/haskell-nix-pkgs.nix { inherit inputs system; };

      # Sources: this cluster + sibling leios-trace-hs, with the Agda-generated
      # Haskell sources overlaid into leios-trace-verifier/dist/haskell. The
      # cabal.project at leios-trace-verifier/cabal.project then resolves
      # `dist/haskell` and `../leios-trace-hs` correctly.
      fsSrc = lib.fileset.toSource {
        root = ./..;
        fileset = lib.fileset.unions [
          ./.
          ../leios-trace-hs
        ];
      };
      src = pkgs.runCommand "leios-trace-verifier-haskell-nix-src" { } ''
        mkdir -p $out
        cp -r ${fsSrc}/. $out/
        chmod -R u+w $out
        mkdir -p $out/leios-trace-verifier/dist/haskell
        cp -r ${agda.hsTraceParser}/hs-src/. $out/leios-trace-verifier/dist/haskell/
        chmod -R u+w $out/leios-trace-verifier/dist/haskell
        find $out/leios-trace-verifier/dist/haskell/src/MAlonzo -name "*.hs" -print \
          | sed "s#^$out/leios-trace-verifier/dist/haskell/src/#        #;s#\.hs##;s#/#.#g" \
          >> $out/leios-trace-verifier/dist/haskell/trace-parser.cabal
        mkdir -p $out/leios-trace-verifier/dist/haskell/data
        cp -r ${./conformance-traces}/{config.yaml,topology.yaml,valid,invalid} \
          $out/leios-trace-verifier/dist/haskell/data/
      '';

      project = hnPkgs.haskell-nix.cabalProject' {
        name = "leios-trace-verifier";
        inherit src;
        cabalProjectFileName = "leios-trace-verifier/cabal.project";
        compiler-nix-name = "ghc9101";
        inputMap = {
          "https://chap.intersectmbo.org/" = inputs.CHaP;
        };
        shell.withHoogle = false;
      };
      flake = project.flake { };

      inherit (inputs.leios-spec.packages.${system}) agdaWithPkgs leiosSpec;
      agdaWithDeps = agdaWithPkgs.withPackages (p: [
        p.standard-library
        p.standard-library-classes
        p.standard-library-meta
        p.abstract-set-theory
        p.agda-categories
        p.iog-prelude
        leiosSpec
      ]);
    in
    {
      devShells.dev-leios-trace-verifier = pkgs.mkShell {
        buildInputs = config.pre-commit.settings.enabledPackages ++ [
          pkgs.zlib
        ];
        nativeBuildInputs = [
          hpkgs.ghc
          pkgs.cabal-install
          hpkgs.haskell-language-server
          hpkgs.fourmolu
          pkgs.pkg-config
          pkgs.gnumake
          agdaWithDeps
        ];
        shellHook = ''
          ${config.pre-commit.settings.shellHook}
          echo
          echo "leios-trace-verifier dev shell. Generate sources and build:"
          echo "  make"
        '';
      };

      legacyPackages.leios-trace-verifier = flake;
    };
}
