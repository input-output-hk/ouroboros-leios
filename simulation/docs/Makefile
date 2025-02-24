
all: sim-realism.pdf

%.pdf: %.tex
	latexmk -bibtex -pdf $<

# Example deps:
sim-realism.pdf: IB-0.5-vs-ideal-vs-fitted-fig.eps  \
		 IB-0.98-vs-ideal-vs-fitted-fig.eps \
		 EB-0.5-vs-ideal-vs-fitted-fig.eps \
		 EB-0.98-vs-ideal-vs-fitted-fig.eps \
		 VT-0.5-vs-ideal-vs-fitted-fig.eps \
		 VT-0.98-vs-ideal-vs-fitted-fig.eps \
		 RB-0.5-vs-ideal-vs-fitted-fig.eps \
		 RB-0.98-vs-ideal-vs-fitted-fig.eps \


clean:
	latexmk -CA

CDFSSCRIPT = ../gnuplot/latency_cdfs.gp
CDFSPLOT = gnuplot -e "set terminal postscript eps enhanced color; set output '$@'" -c $(CDFSSCRIPT)



SHORT_LEIOS = cabal run ols -- sim --output-seconds="$(SIM_SECONDS)" --output-file="$@" short-leios --no-log

%/sim-data.json: %/config.yaml %/topology.yaml
	$(SHORT_LEIOS) -l "$(word 1, $^)" -t "$(word 2, $^)" +RTS -s

## TODO: add mode to `report-data` to list outputs instead, so we can get rid of the proxy file, and have more precise requirements.
.PRECIOUS: %/.ran-report-data
%/.ran-report-data: %/report-config.yaml %/sim-data.json
	cabal run ols -- report-data -o "$(dir $@)" -c $^
	touch "$@"

.SECONDEXPANSION:

%-vs-ideal-fig.eps: $(CDFSSCRIPT) $$(dir $$@).ran-report-data
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal.csv" ideal

%-vs-ideal-vs-fitted-fig.eps: $(CDFSSCRIPT) scenario1/.ran-report-data scenario1-fitted-hops/.ran-report-data
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "scenario1/$*.csv" simulation "scenario1/$*-ideal.csv" ideal "scenario1-fitted-hops/$*-ideal.csv" ideal-fitted

scenario1/sim-data.json: SIM_SECONDS=300
