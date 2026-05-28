{
  description = "Jupyter dev shell for the Linear Leios ΔQ analysis notebooks";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Python with the libraries the notebooks import, plus the Jupyter stack.
        pythonEnv = pkgs.python3.withPackages (
          ps: with ps; [
            # analysis libraries used by the notebooks
            numpy
            scipy
            matplotlib
            # Jupyter runtime + tooling
            notebook # `jupyter notebook`
            jupyterlab # `jupyter lab` (built-in table-of-contents sidebar)
            ipykernel
            nbconvert # headless execution / export
            nbformat
            jupytext # optional: .md <-> .ipynb conversion
          ]
        );
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ pythonEnv ];
          shellHook = ''
            echo "Jupyter environment ready (Python ${pkgs.python3.version})."
            echo "  jupyter notebook   # classic notebook UI"
            echo "  jupyter lab        # JupyterLab (TOC sidebar)"
            echo "Data paths in the derivation notebooks are relative to this directory."
          '';
        };
      }
    );
}
