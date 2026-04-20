{
  inputs,
  self,
  lib,
  ...
}:
{
  perSystem =
    { system, ... }:

    lib.optionalAttrs (system == "x86_64-linux") (
      let
        inherit (inputs) nixpkgs;

        overlay = _next: prev: {
          haskell = prev.haskell // {
            packageOverrides = _hnext: hprev: {
              # Include the DeltaQ packages.
              deltaq = hprev.callCabal2nixWithOptions "deltaq" (
                inputs.deltaq-src.outPath + "/lib/deltaq"
              ) "--no-check" { };
              probability-polynomial = hprev.callCabal2nixWithOptions "probability-polynomial" (
                inputs.deltaq-src.outPath + "/lib/probability-polynomial"
              ) "--no-check" { };
              # Use a more recent version of `lattices` than is available in the curated Nix package set.
              lattices = hprev.callPackage (
                {
                  mkDerivation,
                  base,
                  containers,
                  deepseq,
                  hashable,
                  integer-logarithms,
                  lib,
                  QuickCheck,
                  quickcheck-instances,
                  tagged,
                  tasty,
                  tasty-quickcheck,
                  transformers,
                  universe-base,
                  universe-reverse-instances,
                  unordered-containers,
                }:
                mkDerivation {
                  pname = "lattices";
                  version = "2.2.1";
                  sha256 = "27063f2343b1547033cd59f61b27f797041ed0c25c921f253ce82dc6fffa7666";
                  libraryHaskellDepends = [
                    base
                    containers
                    deepseq
                    hashable
                    integer-logarithms
                    QuickCheck
                    tagged
                    transformers
                    universe-base
                    universe-reverse-instances
                    unordered-containers
                  ];
                  testHaskellDepends = [
                    base
                    containers
                    QuickCheck
                    quickcheck-instances
                    tasty
                    tasty-quickcheck
                    transformers
                    universe-base
                    universe-reverse-instances
                    unordered-containers
                  ];
                  homepage = "http://github.com/phadej/lattices/";
                  description = "Fine-grained library for constructing and manipulating lattices";
                  license = lib.licenses.bsd3;
                }
              ) { };
              # Sadly, we need to loosen the dependency constraint that `Chart-cairo` has on `time`.
              Chart-cairo = hprev.callPackage (
                {
                  mkDerivation,
                  array,
                  base,
                  cairo,
                  Chart,
                  colour,
                  data-default-class,
                  lens,
                  lib,
                  mtl,
                  old-locale,
                  operational,
                  time,
                }:
                mkDerivation {
                  pname = "Chart-cairo";
                  version = "1.9.4.1";
                  sha256 = "27cbc2f1237b739eb60c6c470a9324b7ab63974f33116411ea4c2f347ca22074";
                  prePatch = ''
                    sed -e '/, time/s/ >=.*$//' -i Chart-cairo.cabal
                  '';
                  libraryHaskellDepends = [
                    array
                    base
                    cairo
                    Chart
                    colour
                    data-default-class
                    lens
                    mtl
                    old-locale
                    operational
                    time
                  ];
                  homepage = "https://github.com/timbod7/haskell-chart/wiki";
                  description = "Cairo backend for Charts";
                  license = lib.licenses.bsd3;
                }
              ) { };
            };
          };
        };

        pkgs = import nixpkgs {
          inherit system;
          overlays = [ overlay ];
        };

        inherit (inputs.jupyenv.lib.${system}) mkJupyterlabNew;

        jupyterlab = mkJupyterlabNew (
          { ... }:
          {
            inherit nixpkgs;
            imports = [ (import ./kernels.nix { inherit pkgs; }) ];
          }
        );

        docker = pkgs.dockerTools.buildImage {
          name = "jupyter-deltaq";
          copyToRoot = pkgs.buildEnv {
            name = "image-root";
            paths = [
              pkgs.dockerTools.usrBinEnv
              pkgs.dockerTools.binSh
              pkgs.bash
              pkgs.coreutils
              pkgs.nodejs_18
              jupyterlab
            ];
            pathsToLink = [ "/bin" ];
          };
          runAsRoot = ''
            #!${pkgs.runtimeShell}
            ${pkgs.dockerTools.shadowSetup}
            groupadd -r deltaq
            useradd -r -g deltaq deltaq
            mkdir -p /home/deltaq/examples
            chown -R deltaq:deltaq /home/deltaq
            mkdir -p /usr/bin
            ln -s /bin/env /usr/bin/env
          '';
          extraCommands = ''
            #!${pkgs.runtimeShell}
            chmod 0777 tmp
            mkdir -p home/deltaq/examples
            cp -r ${self}/analysis/deltaq/examples home/deltaq/
          '';
          config = {
            User = "deltaq";
            WorkingDir = "/home/deltaq";
            Cmd = [
              "${jupyterlab}/bin/jupyter-lab"
              "--no-browser"
              "--ip=0.0.0.0"
              "--port=8888"
              "--NotebookApp.token=deltaq"
            ];
            ExposedPorts = {
              "8888" = { };
            };
          };
        };

      in
      {
        packages = {
          inherit jupyterlab docker;
        };

        apps.jupyterlab = {
          program = "${jupyterlab}/bin/jupyter-lab";
          type = "app";
        };
      }
    );
}
