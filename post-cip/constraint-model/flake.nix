{
  description = "Mathematical Modeling Environment (Python + OR-Tools + HiGHS)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          # 1. Packages available in the environment
          buildInputs = with pkgs; [
            python3
            highs
            cbc
            # Libraries often needed by Python wheels
            stdenv.cc.cc.lib  # libstdc++
            zlib              # libz
          ];

          # 2. Shell Hook to set up venv and library paths
          shellHook = ''
            echo "🛠️  Setting up OR-Tools Environment..."

            # --- A. Setup Venv ---
            if [ ! -d ".venv" ]; then
              echo "Creating new virtual environment in .venv..."
              python3 -m venv .venv
            fi
            source .venv/bin/activate

            # Ensure pip is installed
            if ! command -v pip &> /dev/null; then
               python -m ensurepip
            fi

            # --- B. Fix Binary Linking (The Critical Fix) ---
            # This makes the C++ standard library available to pip-installed wheels (numpy, ortools)
            export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib:${pkgs.zlib}/lib:$LD_LIBRARY_PATH
            
            # Also include HiGHS/CBC libs if you use them via ctypes later
            export LD_LIBRARY_PATH=${pkgs.highs}/lib:${pkgs.cbc}/lib:$LD_LIBRARY_PATH

            echo "✅ Environment ready!"
            echo "   Python: $(python --version)"
            echo "   LD_LIBRARY_PATH set for libstdc++ and zlib."
            echo "   Run: pip install pulp ortools networkx numpy"
          '';
        };
      }
    );
}
