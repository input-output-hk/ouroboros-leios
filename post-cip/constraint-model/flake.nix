{
  description = "Mathematical Modeling Environment (Python + HiGHS + CBC)";

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
          # The packages available in the environment
          buildInputs = with pkgs; [
            python3
            highs
            cbc
          ];

          # This script runs every time you enter 'nix develop'
          shellHook = ''
            echo "🛠️  Setting up MIP Environment..."

            # 1. Create venv if it doesn't exist
            if [ ! -d ".venv" ]; then
              echo "Creating new virtual environment in .venv..."
              python3 -m venv .venv
            fi

            # 2. Activate the venv
            source .venv/bin/activate

            # 3. Ensure pip is installed/upgraded
            # (Nix's python sometimes creates venvs without pip, ensures it works)
            if ! command -v pip &> /dev/null; then
               python -m ensurepip
            fi

            # 4. Set LD_LIBRARY_PATH so Python ctypes can find solver libraries if needed
            export LD_LIBRARY_PATH=${pkgs.highs}/lib:${pkgs.cbc}/lib:$LD_LIBRARY_PATH

            echo "✅ Environment ready! (Python $(python --version), HiGHS $(highs --version))"
            echo "   Type 'pip install pulp' to get started."
          '';
        };
      }
    );
}
