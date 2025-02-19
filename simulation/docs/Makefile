
all: sim-realism.pdf

%.pdf: %.tex
	latexmk -bibtex -pdf $<

clean:
	latexmk -CA

CDFSPLOT = gnuplot -e "set terminal postscript eps enhanced color; set output '$@'" -c ../gnuplot/latency_cdfs.gp

%-vs-ideal-fig.eps: %.csv %-ideal.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$<" simulation "$(word 2, $^)" ideal

# Example deps:
# sim-realism.pdf: fig1.eps
