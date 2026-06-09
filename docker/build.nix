# Statically-linked cardano-node + cardano-cli from the
# 'cardano-node-leios' flake input (the leios-prototype branch), plus a
# thin Docker image wrapping them. Exposed via:
#
#   nix build .#cardano-node-static
#   nix build .#cardano-cli-static
#   nix build .#cardano-node-leios-image   # streamed tarball; pipe into `docker load`
#
# CI publishes the image as ghcr.io/input-output-hk/ouroboros-leios/cardano-node-leios
# on every push to main. Scenario images (cardano-node-antithesis,
# cardano-node-testnet) layer their configs/scripts on top.
# `inputs` is a top-level (not perSystem) module argument in
# flake-parts — perSystem only sees `inputs'` (per-system flattened),
# which auto-flattens standard outputs (packages / devShells / apps /
# …) but NOT custom ones like `hydraJobs`. We need the raw `inputs` to
# reach into `cardano-node-leios.hydraJobs.${system}.musl`, so we
# accept it at the top of this module and use it inside perSystem.
{ inputs, ... }:
{
  perSystem =
    {
      pkgs,
      lib,
      system,
      ...
    }:
    lib.optionalAttrs (system == "x86_64-linux") (
      let
        # The cardano-node flake exposes its statically-linked
        # x86_64-linux builds under hydraJobs.<system>.musl.<exe>; they
        # come from project.projectCross.musl64 in nix/haskell.nix and
        # are fully static (no glibc, no dynamic loader).
        muslJobs = inputs.cardano-node-leios.hydraJobs.${system}.musl;
      in
      {
        packages = {
          cardano-node-static = muslJobs.cardano-node;
          cardano-cli-static = muslJobs.cardano-cli;

          # Streamed layered image: `nix build .#cardano-node-leios-image`
          # produces a script that, when run, writes the image tarball to
          # stdout. Typical use:
          #
          #   $(nix build .#cardano-node-leios-image --print-out-paths) | docker load
          #
          # The image carries only the two binaries plus minimal /etc
          # files (ca-certs, /etc/passwd, /etc/group, tmp dirs). No shell,
          # no package manager — overlays add what they need.
          cardano-node-leios-image = pkgs.dockerTools.streamLayeredImage {
            name = "cardano-node-leios";
            tag = "latest";
            contents = [
              muslJobs.cardano-node
              muslJobs.cardano-cli
              # ca-certificates for TLS to bootstrap relays / Hydra / etc.
              pkgs.cacert
              # /etc/passwd + /etc/group + /tmp so things that expect a
              # POSIX-ish layout don't fall over.
              pkgs.dockerTools.fakeNss
              # Shell + core utils so derived Dockerfiles can RUN chmod /
              # mkdir / etc., and for ad-hoc debugging via `docker exec`.
              pkgs.bashInteractive
              pkgs.coreutils
            ];
            config = {
              Entrypoint = [ "/bin/cardano-node" ];
              Env = [
                "SSL_CERT_FILE=/etc/ssl/certs/ca-bundle.crt"
                "PATH=/bin"
              ];
            };
          };
        };
      }
    );
}
