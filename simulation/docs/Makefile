
all: sim-realism.pdf

%.pdf: %.tex
	latexmk -bibtex -pdf $<

# Example deps:
sim-realism.pdf: scenario1/IB-0.5-vs-ideal-vs-fitted-fig.eps  \
		 scenario1/IB-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1/EB-0.5-vs-ideal-vs-fitted-fig.eps \
		 scenario1/EB-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1/VT-0.5-vs-ideal-vs-fitted-fig.eps \
		 scenario1/VT-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1/RB-0.5-vs-ideal-vs-fitted-fig.eps \
		 scenario1/RB-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1-send-recv/VT-0.5-vs-ideal-vs-fitted-fig.eps \
		 scenario1-send-recv/VT-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1-big-votes/VT-0.5-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes/VT-0.98-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes-send-recv/VT-0.5-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes-send-recv/VT-0.98-vs-ideal-4-hops-fig.eps \


clean:
	latexmk -CA

MAIN_SCENARIOS=scenario1 scenario2 scenario3 scenario4 scenario5 scenario6

define main_scenario_template =
sim-realism.pdf: $(1)/IB-0.5-vs-ideal-vs-fitted-fig.eps \
                 $(1)/IB-0.98-vs-ideal-vs-fitted-fig.eps \
		 $(1)/EB-0.5-vs-ideal-vs-fitted-fig.eps \
		 $(1)/EB-0.98-vs-ideal-vs-fitted-fig.eps \
		 $(1)/VT-0.5-vs-ideal-vs-fitted-fig.eps \
		 $(1)/VT-0.98-vs-ideal-vs-fitted-fig.eps \
		 $(1)/RB-0.5-vs-ideal-vs-fitted-fig.eps \
		 $(1)/RB-0.98-vs-ideal-vs-fitted-fig.eps
endef

$(foreach s,$(MAIN_SCENARIOS),$(eval $(call main_scenario_template,$(s))))

CDFSSCRIPT = ../gnuplot/latency_cdfs.gp
CDFSPLOT = gnuplot -e "set terminal postscript eps enhanced color; set output '$@'" -c $(CDFSSCRIPT)


SHORT_LEIOS = cabal run ols -- sim --output-seconds="$(SIM_SECONDS)" --output-file="$@" short-leios --no-log

%/sim-data.json: %/config.yaml %/topology.yaml
	$(SHORT_LEIOS) -l "$(word 1, $^)" -t "$(word 2, $^)" +RTS -s

%/sim-data.json: SIM_SECONDS=300

all_sims: $(shell ls */report-config.yaml | sed -e's/report-config.yaml/sim-data.json/')

SCENARIOS = $(shell ls */report-config.yaml | sed -e's/report-config.yaml//')

## Would be great to use a grouped targets rule, but that requires make 4.3.
## TODO: cache targets?
define scenario_template =
 .PRECIOUS:
 $(shell cabal run -v0 ols -- report-data -o $(1) -c $(1)report-config.yaml --print-targets-only dummy) : $(1).ran-report-data
endef

$(foreach s,$(SCENARIOS),$(eval $(call scenario_template,$(s))))

.PRECIOUS:
%/.ran-report-data: %/report-config.yaml %/sim-data.json
	cabal run ols -- report-data -o "$(dir $@)" -c $^
	touch "$@"

%-vs-ideal-fig.eps: $(CDFSSCRIPT) %.csv %-ideal.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal.csv" ideal

%-vs-ideal-vs-fitted-fig.eps: $(CDFSSCRIPT) %.csv %-ideal.csv %-ideal-fitted.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal.csv" ideal "$*-ideal-fitted.csv" ideal-fitted

%-vs-ideal-4-hops-fig.eps: $(CDFSSCRIPT) %.csv %-ideal-4-hops.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal-4-hops.csv" ideal-4-hops
