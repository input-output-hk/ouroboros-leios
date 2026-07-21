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
            dejavu
            enumitem
            environ
            etoolbox
            eurosym
            fontspec
            jknapltx
            lm-math
            newunicodechar
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
        # built-in latex template (block `margins` in latex/base.tex.j2) and
        # disables LaTeX's automatic section numbering (the notebook headings
        # carry their own numbers).
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
          \setcounter{secnumdepth}{-2}
          % Markdown code fences (ASCII diagrams) are up to ~114 chars wide;
          % at 11pt only ~94 monospace chars fit the line, so render verbatim
          % blocks at \footnotesize (~114 chars).
          \makeatletter
          \def\verbatim@font{\normalfont\ttfamily\footnotesize}
          \makeatother
          % H4/H5 headings (\paragraph/\subparagraph) are run-in by default;
          % give them a positive afterskip so body text starts on a new line.
          \makeatletter
          \renewcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
            {3.25ex \@plus 1ex \@minus .2ex}%
            {0.75ex \@plus .2ex}%
            {\normalfont\normalsize\bfseries}}
          \renewcommand\subparagraph{\@startsection{subparagraph}{5}{\z@}%
            {3.25ex \@plus 1ex \@minus .2ex}%
            {0.75ex \@plus .2ex}%
            {\normalfont\normalsize\bfseries}}
          \makeatother
          % Latin Modern text/mono fonts lack ≤, ≈, Greek, sub/superscripts and
          % box-drawing glyphs, so XeTeX drops them silently.  Map them: math
          % symbol in prose, DejaVu Sans Mono in verbatim (scaled 0.872 so its
          % 0.602em advance matches LM Mono's 0.525em and columns stay aligned).
          \usepackage{newunicodechar}
          \newfontfamily\ttfallback{DejaVuSansMono.ttf}[Scale=0.872]
          \makeatletter
          \newcommand*\symfallback[2]{%
            \ifmmode #1\else
              \ifdefstrequal{\f@family}{\ttdefault}%
                {{\ttfallback\char"#2\relax}}%
                {\ensuremath{#1}}%
            \fi}
          \makeatother
          \newunicodechar{≤}{\symfallback{\leq}{2264}}
          \newunicodechar{≥}{\symfallback{\geq}{2265}}
          \newunicodechar{≈}{\symfallback{\approx}{2248}}
          \newunicodechar{π}{\symfallback{\pi}{03C0}}
          \newunicodechar{σ}{\symfallback{\sigma}{03C3}}
          \newunicodechar{τ}{\symfallback{\tau}{03C4}}
          \newunicodechar{⁶}{\symfallback{^{6}}{2076}}
          \newunicodechar{₀}{\symfallback{_{0}}{2080}}
          \newunicodechar{₁}{\symfallback{_{1}}{2081}}
          \newunicodechar{₂}{\symfallback{_{2}}{2082}}
          \newunicodechar{─}{{\ttfallback\char"2500\relax}}
          \newunicodechar{│}{{\ttfallback\char"2502\relax}}
          \newunicodechar{┌}{{\ttfallback\char"250C\relax}}
          \newunicodechar{└}{{\ttfallback\char"2514\relax}}
          \newunicodechar{┤}{{\ttfallback\char"2524\relax}}
          ((* endblock margins *))

          ((=- style_jupyter wraps stream output at charlim=80, which mangles
              wide ASCII tables.  Emit the text unwrapped instead and shrink
              the font to fit the widest line (11pt budgets: ~94 chars at
              normal size, ~114 footnotesize, ~129 scriptsize, ~147 at 7pt). -=))
          ((* block stream *))
          ((*- set maxw = output.text.splitlines() | map('length') | max -*))
          \begin{Verbatim}[commandchars=\\\{\}((*- if maxw > 128 -*)), fontsize=\fontsize{7}{8.5}\selectfont((*- elif maxw > 114 -*)), fontsize=\scriptsize((*- elif maxw > 90 -*)), fontsize=\footnotesize((*- endif -*))]
          ((( output.text | escape_latex | strip_trailing_newline | ansi2latex )))
          \end{Verbatim}
          ((* endblock stream *))
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
