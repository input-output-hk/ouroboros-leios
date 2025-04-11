.PHONY: all
all: network-spec.pdf

network-spec.pdf: miniprotocols.tex references.bib

%.pdf: %.tex
	latexmk -bibtex -pdf $<

clean:
	latexmk -CA
