{
  description = "Consensus algorithm evaluation for midnight";

  inputs = {
    nixpkgs.url = "github:Nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = { allowUnfree = true; };
        };
        rootBuildInputs = with pkgs; [
            nodejs
            (python3.withPackages (ps: with ps; [
              pypdf
              matplotlib
              numpy
              # scikit-learn — used by experiments/design-space-poc/intrinsic_dim.py
              # for the KD-tree 2-nearest-neighbor query that powers the TwoNN
              # intrinsic-dimension estimator.
              scikit-learn
              # SALib + SciPy — used by experiments/design-space-saltelli-small/
              # for the Python-side reference Saltelli implementation, which
              # validates the streaming Lean implementation at a small N.
              salib
              scipy
              pandas
              # UMAP + kmapper + ripser — design-space topology exploration
              # suite, complementing the TwoNN intrinsic-dim estimator.
              # UMAP for 2-D visualizations of the feasible region;
              # kmapper for the Mapper algorithm (scalable graph-based
              # topology); ripser for full Vietoris-Rips persistent
              # homology on small subsamples.
              #
              # HDBSCAN intentionally omitted: nixpkgs's hdbscan-0.8.41
              # derivation fails to build (a no-op `replace-assert_raises`
              # patch can't apply against upstream's already-updated source).
              # Use `sklearn.cluster.HDBSCAN` instead — same algorithm, in
              # scikit-learn ≥ 1.3 and recommended for new code.
              umap-learn
              kmapper
              ripser
              # Bayesian-optimization stack — experiments/bo-optimization/
              # drives multi-objective BO (qNEHVI / qParEGO) over the Lean
              # design-space model via a native-subprocess oracle (mnc-eval).
              # BoTorch builds on top of GPyTorch and PyTorch; pyyaml is for
              # scenario files; pytest for the Python-side oracle tests.
              # wasmtime is kept for the (currently-impeded) in-process WASM
              # transport story — Emscripten legacy-EH means modern wasmtime
              # rejects the artifact today; the package is on the path so
              # the pivot is documented, not because it's loadable.
              wasmtime       # in-process WASM runtime — currently unused (see lessons-learned.md)
              torch          # PyTorch (BoTorch's tensor + autograd backend)
              gpytorch       # Gaussian-process surrogate models
              botorch        # multi-objective BO acquisition functions
              pyyaml
              pytest
              # Glueviz — ggobi-class linked-view multi-pane data explorer
              # for the BO output. Loads the history CSV emitted by
              # experiments/bo-optimization/export_glue.py; brushing in
              # any view propagates to all linked views, so e.g.
              # selecting the Pareto-front cluster in a 3D scatter
              # highlights the same rows in a parallel-coordinates view
              # of the 12 constraint slacks. Pulls Qt + matplotlib in
              # transitively. See experiments/bo-optimization/README.md.
              glueviz
              # Parquet reader for the walker's archives — an alternative to
              # the CLI `duckdb` below when we want to stay in Python (e.g.,
              # combine with pandas / matplotlib for archive spot-checks).
              pyarrow
              # psrecord — CPU/memory time-series sampler used by
              # experiments/instrumented-node/scripts/run-preprod.sh alongside
              # GNU time. Pointed at a running process PID; emits a log +
              # matplotlib plot of CPU % and RSS over the run.
              psrecord
            ]))
            pandoc
            gnumake
            # GNU time — the `time -v` binary (not the bash `time` keyword).
            # Used by experiments/instrumented-node/scripts/run-preprod.sh to
            # capture aggregate user/system CPU + wall-clock + peak RSS + I/O
            # for the instrumented preprod-sync run.
            time
            poppler-utils  # pdftotext, pdfinfo, pdftoppm — needed for PDF reading
            ghostscript    # PDF manipulation and conversion
            imagemagick    # SVG → PNG conversion for slide-deck figures (see artifacts/phase-1-slides/figures/)
            jq             # JSON processing
            # DuckDB — quick SQL over Parquet without a Python dep chain.
            # Used for spot-checking the walker's archives (both the
            # `walk`-produced and `process-instrumented`-produced ones)
            # against each other and against ad-hoc analytical queries
            # in experiments/preprod-txs/.
            duckdb
            curl
            yamllint       # YAML linter (workflow files, pre-commit checks)
            shellcheck     # Bash linter (experiments/runs/shard.sh and friends)
            statix         # Nix antipattern linter (this flake.nix)
            # Lean 4 toolchain — elan manages per-project Lean versions via
            # the `lean-toolchain` file in each project subdir. lean2wasm
            # pins `leanprover/lean4:v4.6.1`; see experiments/lean2wasm/.
            elan
            # Rust toolchain — rustup manages per-project Rust versions via
            # the `rust-toolchain.toml` file in each project subdir, in the
            # same pattern as elan/Lean above. Used by
            # experiments/preprod-txs/scraper/ (ticket #151, sub-issue of
            # #139); the midnight-ledger crates we'll pull in later may pin
            # a specific rustc release, so rustup is preferred over the
            # stable-only nixpkgs `rustc` + `cargo` pair.
            rustup
            # Substrate build toolchain — required to build the vendored
            # midnight-node in experiments/instrumented-node/. Substrate's
            # wasm-builder invokes `-fuse-ld=lld` (fails without lld on
            # PATH), and secp256k1-sys's build.rs compiles C code for the
            # wasm32v1-none target using `-mcpu=mvp -mmutable-globals`
            # (which GCC doesn't understand — needs clang). See
            # experiments/instrumented-node/lessons-learned.md for the
            # trace that motivated adding these.
            llvmPackages_19.clang  # wasm32-target C compilation for secp256k1-sys and friends
            llvmPackages_19.lld    # rustc's default -fuse-ld=lld — required for substrate builds
            cmake                  # some substrate crates (jsonrpsee, rocksdb-sys) need it
            pkg-config             # ditto — used to locate system libraries
            openssl.dev            # crate `openssl-sys` looks up here via pkg-config
            # Emscripten — required by lean2wasm for Lean → WASM compilation.
            # Version pin delegated to nixpkgs unstable; revisit if the spike
            # (ticket #70) finds compatibility issues with Lean 4.6.1.
            emscripten
            # TypeScript — used by experiments/lean2wasm/ for the browser glue
            # (index.ts → dist/index.js). `npm` is provided by the `nodejs`
            # entry above and not listed separately.
            typescript
            # VS Code (proprietary Microsoft build, non-free). Permitted by
            # `allowUnfree = true` above. Use `vscodium` instead if a fully
            # open-source build is required for some context.
            vscode
            # Compression toolchain — experiments/block-compression/ (ticket
            # #244) measures the compressibility of Midnight transaction/proof
            # bytes across the standard compressor families. Most of these are
            # already on the base PATH; pinned here for reproducibility. `zpaq`
            # is the one addition: a context-mixing compressor used only as an
            # entropy-floor reference (impractically slow, never a deployment
            # option) to bound how incompressible the ZK-proof bytes really are.
            gzip
            bzip2
            xz
            zstd
            lz4
            brotli
            mermaid-cli
            zpaq
            (rWrapper.override {
              packages = with rPackages; [
                ggplot2
                ggExtra
                svglite
                # Used by experiments/runs/*.R — see
                # design-space-model/experiments/runs/README.md.
                data_table      # fast data frames; rpart's data.frame input
                rpart           # classification / regression trees
                rpart_plot      # rendering for rpart fits (dendrogram.R)
                R_utils         # lets fread() consume .gz directly
              ];
            })
        ];

        rootShellHook = ''
            export PS1=$(printf '\n\001\033[1;32m\002[nix develop:\\w]\\$\001\033[0m\002 ')
            # elan stores per-toolchain state under $ELAN_HOME (default
            # ~/.elan). Override here if a project-local cache is preferred.
            export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
            export PATH="$ELAN_HOME/bin:$PATH"
            # rustup stores per-toolchain state under $RUSTUP_HOME (default
            # ~/.rustup), and installs cargo/rustc shims under
            # $CARGO_HOME/bin (default ~/.cargo/bin). Same per-user cache
            # pattern as elan/Emscripten. `rustup default stable` on first
            # entry to populate; individual projects can pin via
            # rust-toolchain.toml.
            export RUSTUP_HOME="''${RUSTUP_HOME:-$HOME/.rustup}"
            export CARGO_HOME="''${CARGO_HOME:-$HOME/.cargo}"
            export PATH="$CARGO_HOME/bin:$PATH"
            # Emscripten needs a writable cache; the nixpkgs wrapper points
            # at a read-only store path by default. Redirect to a per-user
            # cache directory.
            export EM_CACHE="''${EM_CACHE:-$HOME/.cache/emscripten}"
            # Substrate build tooling. bindgen-using crates (rocksdb-sys,
            # secp256k1-sys) need $LIBCLANG_PATH so they can locate libclang.
            # secp256k1-sys's build.rs compiles C for wasm32v1-none; point
            # CC_wasm32v1_none / AR_wasm32v1_none at LLVM tooling so the
            # -mcpu=mvp / -mmutable-globals flags parse correctly.
            #
            # NB: use the UNWRAPPED clang for the wasm-target CC. Nix's
            # cc-wrapper injects hardening flags (`-fzero-call-used-regs=used-gpr`)
            # that clang rejects when compiling for wasm32-unknown-unknown.
            # It also silently pulls in host glibc headers, which then fail
            # on `gnu/stubs-32.h` because we don't have 32-bit stubs. The
            # unwrapped clang avoids both.
            #
            # BUT — nix splits the unwrapped clang derivation into `bin`
            # (the compiler binary) and `.lib` (the resource-dir headers
            # like stddef.h). Clang's baked-in -resource-dir points inside
            # its bin output where headers don't exist. Override via
            # CFLAGS_wasm32v1_none to redirect at the .lib output.
            #
            # The `19` version segment tracks llvmPackages_19; bump both
            # together on LLVM upgrades.
            #
            # See experiments/instrumented-node/lessons-learned.md.
            export LIBCLANG_PATH="${pkgs.llvmPackages_19.libclang.lib}/lib"
            export CC_wasm32v1_none="${pkgs.llvmPackages_19.clang-unwrapped}/bin/clang"
            export AR_wasm32v1_none="${pkgs.llvmPackages_19.llvm}/bin/llvm-ar"
            export CFLAGS_wasm32v1_none="-resource-dir=${pkgs.llvmPackages_19.clang-unwrapped.lib}/lib/clang/19"
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = rootBuildInputs;
          shellHook = rootShellHook;
        };
      }
    );
}
