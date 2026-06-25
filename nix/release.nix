# Release artifacts: cardano-node + cardano-cli from the
# 'cardano-node-leios' flake input (the leios-prototype branch),
# packaged for distribution. Exposed via:
#
#   nix build .#cardano-node-static          # x86_64-linux only
#   nix build .#cardano-cli-static           # x86_64-linux only
#   nix build .#cardano-node-leios-image     # x86_64-linux only; pipe into `docker load`
#   nix build .#cardano-node-release         # x86_64-linux + aarch64-darwin
#                                            # relocatable release tarball
#
# CI publishes the image as ghcr.io/input-output-hk/ouroboros-leios/cardano-node-leios
# on every push to main, and uploads the release tarball as a workflow
# artifact (attaching it to a draft GitHub release on tag pushes).
# Scenario images (antithesis-cardano-node-burst,
# antithesis-cardano-node-devnet, cardano-node-testnet) layer their
# configs/scripts on top.
# `inputs` is a top-level (not perSystem) module argument in
# flake-parts — perSystem only sees `inputs'` (per-system flattened),
# which auto-flattens standard outputs (packages / devShells / apps /
# …) but NOT custom ones like `hydraJobs`. We need the raw `inputs` to
# reach into `cardano-node-leios.hydraJobs.${system}.{musl,native}`, so
# we accept it at the top of this module and use it inside perSystem.
{ inputs, ... }:
{
  perSystem =
    {
      pkgs,
      lib,
      system,
      ...
    }:
    let
      # Release tarball naming, used by both platforms so consumers see a
      # consistent `cardano-node-leios-<system>.tar.gz` with the same
      # `cardano-node-leios-<system>/bin/...` layout inside.
      releaseName = "cardano-node-leios-${system}";

      # The cardano-node flake exposes its statically-linked x86_64-linux
      # builds under hydraJobs.x86_64-linux.musl.<exe>; they come from
      # project.projectCross.musl64 in nix/haskell.nix and are fully
      # static (no glibc, no dynamic loader). `or null` keeps this safe
      # to reference on other systems — Nix is lazy and only the linux
      # branches below actually dereference muslJobs.
      muslJobs = inputs.cardano-node-leios.hydraJobs.${system}.musl or null;
    in
    {
      # Single packages attrset built from two optionalAttrs blocks merged
      # AT THE LEAF level (one big attribute set), rather than two parent
      # blocks each setting `packages = ...` (where `//` is shallow and
      # would silently drop the earlier entries).
      packages =
        lib.optionalAttrs (system == "x86_64-linux") {
          cardano-node-static = muslJobs.cardano-node;
          cardano-cli-static = muslJobs.cardano-cli;
          # tx-centrifuge lives on a different cardano-node ref
          # (bench/leios snapshot) than the rest of the binaries; we
          # intentionally keep it pinned separately. Same hydraJobs shape.
          tx-centrifuge-static = inputs.cardano-node-tx-centrifuge.hydraJobs.${system}.musl.tx-centrifuge;

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
        }
        //
          lib.optionalAttrs
            (lib.elem system [
              "x86_64-linux"
              "aarch64-darwin"
            ])
            {
              # Single release-tarball entry, with the per-system switch inside
              # the expression (rather than a separate top-level optionalAttrs
              # block per system, which would have to merge `packages` attrsets
              # at the parent level and silently drop entries).
              cardano-node-release =
                if system == "x86_64-linux" then
                  # Static musl binaries: no /nix/store references, just bundle.
                  pkgs.runCommand "${releaseName}.tar.gz" { } ''
                    mkdir -p "${releaseName}/bin"
                    cp ${muslJobs.cardano-node}/bin/cardano-node "${releaseName}/bin/"
                    cp ${muslJobs.cardano-cli}/bin/cardano-cli   "${releaseName}/bin/"
                    chmod +x "${releaseName}/bin"/*
                    mkdir -p $out
                    tar -czf "$out/${releaseName}.tar.gz" "${releaseName}"
                  ''
                else
                  # aarch64-darwin: repackage upstream's cardano-node-macos
                  # tarball under our naming scheme. Upstream runs `rewrite-libs`
                  # over the dylib paths so the binaries don't reference
                  # /nix/store; we only extract, rename the wrapper directory,
                  # and re-tar (the binaries themselves are untouched, so the
                  # patching is preserved).
                  let
                    upstream = inputs.cardano-node-leios.hydraJobs.${system}.native.cardano-node-macos;
                  in
                  pkgs.runCommand "${releaseName}.tar.gz" { } ''
                    tmp=$(mktemp -d)
                    tar -xzf ${upstream}/*.tar.gz -C "$tmp"
                    # Upstream uses cardano-node-<ver>-macos/ as the wrapper dir.
                    upstream_dir=$(ls "$tmp")
                    mv "$tmp/$upstream_dir" "$tmp/${releaseName}"
                    mkdir -p $out
                    tar -czf "$out/${releaseName}.tar.gz" -C "$tmp" "${releaseName}"
                  '';
            };
    };
}
