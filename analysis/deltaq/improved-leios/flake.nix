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

        # XeTeX + the LaTeX packages nbconvert's PDF template needs.
        texEnv = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-small
            adjustbox
            collectbox
            enumitem
            environ
            etoolbox
            eurosym
            fontspec
            jknapltx
            lm-math
            parskip
            pdfcol
            pgf
            rsfs
            soul
            tcolorbox
            titling
            trimspaces
            ucs
            ulem
            unicode-math
            upquote
            ;
        };

        # nbconvert template that overrides the default 1in margins of the
        # built-in latex template (block `margins` in latex/base.tex.j2).
        reportTemplate = pkgs.runCommand "nbconvert-report-template" { } ''
          mkdir -p $out/report
          cat > $out/report/conf.json <<'JSON'
          {
            "base_template": "latex",
            "mimetypes": { "text/latex": true }
          }
          JSON
          cat > $out/report/index.tex.j2 <<'TEX'
          ((*- extends 'latex/index.tex.j2' -*))

          ((* block margins *))
          \geometry{verbose,tmargin=0.75in,bmargin=0.75in,lmargin=0.5in,rmargin=0.5in}
          ((* endblock margins *))
          TEX
        '';

        # Report-style PDF of the analysis notebook: markdown + outputs, no code cells.
        makePdf = pkgs.writeShellApplication {
          name = "make-pdf";
          runtimeInputs = [
            pythonEnv
            texEnv
            pkgs.pandoc
          ];
          text = ''
            jupyter nbconvert --to pdf --no-input \
              --template report \
              --TemplateExporter.extra_template_basedirs='${reportTemplate}' \
              --output analysis analysis.ipynb
          '';
        };
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            pythonEnv
            texEnv
            pkgs.pandoc
            makePdf
          ];
          shellHook = ''
            echo "Jupyter environment ready (Python ${pkgs.python3.version})."
            echo "  jupyter notebook   # classic notebook UI"
            echo "  jupyter lab        # JupyterLab (TOC sidebar)"
            echo "  make-pdf           # analysis.ipynb -> analysis.pdf (code cells hidden)"
            echo "Data paths in the derivation notebooks are relative to this directory."
          '';
        };

        apps.pdf = {
          type = "app";
          program = "${makePdf}/bin/make-pdf";
        };
      }
    );
}
