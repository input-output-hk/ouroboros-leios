# Release artifacts from the cardano-node-leios input. Exposed via:
#
#   nix build .#cardano-node-static          # x86_64-linux
#   nix build .#cardano-cli-static           # x86_64-linux
#   nix build .#cardano-node-leios-image     # x86_64-linux; pipe into `docker load`
#   nix build .#cardano-node-release         # x86_64-linux + aarch64-darwin tarball
#
# CI publishes the image to GHCR and attaches the release tarball to
# draft releases on tag pushes. Scenario images (antithesis-*,
# cardano-node-testnet) layer on top of the base image.
#
# We take `inputs` (not `inputs'`) because flake-parts only flattens
# standard outputs per-system, not custom ones like `hydraJobs`.
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
      releaseName = "cardano-node-leios-${system}";

      # Statically-linked x86_64-linux builds (musl, no glibc). `or null`
      # keeps it safe to reference on other systems; Nix is lazy and only
      # the linux branches below dereference it.
      muslJobs = inputs.cardano-node-leios.hydraJobs.${system}.musl or null;
    in
    {
      # Merge both optionalAttrs blocks at the leaf level — a single
      # `packages = ...` so `//` can't silently drop entries.
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
              # Per-system switch inside the expression — keeps the
              # packages attrset a single merge target so future entries
              # can't silently drop each other.
              #
              # Both upstream tarballs have bin/ + share/ at the root and
              # ship the full releaseBins set; we strip down to the two
              # binaries we care about, drop share/, re-tar.
              cardano-node-release =
                let
                  upstream =
                    if system == "x86_64-linux" then
                      inputs.cardano-node-leios.hydraJobs.${system}.musl.cardano-node-linux
                    else
                      inputs.cardano-node-leios.hydraJobs.${system}.native.cardano-node-macos;
                in
                pkgs.runCommand "${releaseName}.tar.gz" { } ''
                  mkdir -p work $out
                  tar -xzf ${upstream}/*.tar.gz -C work

                  rm -rf work/share
                  # Keep the two binaries and every *.dylib — on macOS the
                  # dylibs live next to the executables (referenced as
                  # @executable_path/libfoo) and are shared across release
                  # bins, so we keep them all rather than computing the
                  # exact closure. On linux this matches nothing.
                  find work/bin -mindepth 1 -maxdepth 1 \
                    ! -name cardano-node ! -name cardano-cli \
                    ! -name '*.dylib' \
                    -exec rm {} +

                  tar -czf "$out/${releaseName}.tar.gz" -C work bin
                '';
            };
    };
}
