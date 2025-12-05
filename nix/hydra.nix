# Make default hydraJobs from Flake outputs
# If you have the following checks/devShells/packages
# ├───checks
# │   └───x86_64-linux
# │       ├───check-foo: derivation 'check-foo'
# │       ├───check-bar: derivation 'check-bar'
# │   └───x86_64-darwin
# │       ├───check-foo: derivation 'check-foo'
# │       ├───check-bar: derivation 'check-bar'
# ├───devShells
# │   └───x86_64-linux
# │       ├───dev-foo: development environment 'dev-foo'
# │       ├───dev-bar: development environment 'dev-bar'
# │   └───x86_64-darwin
# │       ├───dev-foo: development environment 'dev-foo'
# │       ├───dev-bar: development environment 'dev-bar'
# └───packages
#     └───x86_64-linux
#         ├───foo: package 'foo'
#         ├───bar: package 'bar'
#     └───x86_64-darwin
#         ├───foo: package 'foo'
#         ├───bar: package 'bar'
# This function will produce hydraJobs as
# ├───hydraJobs
# │   ├───checks
# │   │   ├───check-foo
# │   │   │   └───x86_64-linux: derivation 'check-foo'
# │   │   │   └───x86_64-darwin: derivation 'check-foo'
# │   │   ├───check-bar
# │   │   │   └───x86_64-linux: derivation 'check-bar'
# │   │   │   └───x86_64-darwin: derivation 'check-bar'
# │   ├───devShells
# │   │   ├───dev-foo
# │   │   │   └───x86_64-linux: derivation 'dev-foo'
# │   │   │   └───x86_64-darwin: derivation 'dev-foo'
# │   │   ├───dev-bar
# │   │   │   └───x86_64-linux: derivation 'dev-bar'
# │   │   │   └───x86_64-darwin: derivation 'dev-bar'
# │   └───packages
# │       ├───foo
# │       │   └───x86_64-linux: derivation 'foo'
# │       │   └───x86_64-darwin: derivation 'foo'
# │       ├───bar
# │       │   └───x86_64-linux: derivation 'bar'
# │       │   └───x86_64-darwin: derivation 'bar'
{
  flake,
  lib,
  systems,
  ...
}:
let
  flakeOutputs = [
    "packages"
    "checks"
    "devShells"
  ];
in
lib.genAttrs flakeOutputs (
  flakeOutput:
  lib.foldl' lib.recursiveUpdate { } (
    builtins.map (
      system:
      lib.genAttrs (builtins.attrNames flake.${flakeOutput}.${system}) (drvName: {
        ${system} = flake.${flakeOutput}.${system}.${drvName};
      })
    ) systems
  )
)
