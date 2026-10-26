{
  description = "a minimal Lean 4 model of Linear Leios with a focus on timings";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        # `elan` is the Lean toolchain manager; it reads `lean-toolchain` and fetches
        # exactly that Lean, so Nix pins nothing Lean-specific. git/curl/cacert are
        # what `lake` needs to fetch Mathlib and its olean cache.
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [ elan git curl cacert ];
          shellHook = ''
            export SSL_CERT_FILE="''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}"
            export NIX_SSL_CERT_FILE="$SSL_CERT_FILE"
            cat <<'BANNER'
            lean-leios shell: lake, lean (via elan).
              lake exe cache get   # Mathlib oleans; elan fetches lean-toolchain on first use
              lake build --wfail   # library must build with no warnings and no sorry
            BANNER
          '';
        };
      });
}
