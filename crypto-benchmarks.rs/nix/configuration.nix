{ self, inputs, ...}: {
  perSystem = {system, pkgs, lib, ...}:

    let
      toolchain = with inputs.fenix.packages.${system};
        combine [
          minimal.rustc
          minimal.cargo
          targets.x86_64-unknown-linux-musl.latest.rust-std
          pkgs.tinycbor
        ];

      naersk' = inputs.naersk.lib.${system}.override {
        cargo = toolchain;
        rustc = toolchain;
      };

      cargoToml = builtins.fromTOML (builtins.readFile "${self}/Cargo.toml");
      version = cargoToml.package.version or "0.1.0";

    in rec {
      packages.default = naersk'.buildPackage {
        src = lib.cleanSource "${self}";
        stdenv = pkgs.stdenv;
        doCheck = false;
        copyLibs = true;

        CARGO_BUILD_TARGET = if system == "x86_64-linux" then "x86_64-unknown-linux-musl" else null;
        CARGO_BUILD_RUSTFLAGS = if system == "x86_64-linux" then "-C target-feature=+crt-static" else null;

      };
    };
}
