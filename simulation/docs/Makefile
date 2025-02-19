
all: sim-realism.pdf

%.pdf: %.tex
	latexmk -bibtex -pdf $<

clean:
	latexmk -CA

# Example deps:
# sim-realism.pdf.pdf: fig1.eps
