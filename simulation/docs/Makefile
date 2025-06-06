
all: sim-realism.pdf

%.pdf: %.tex
	latexmk -bibtex -pdf $<

clean:
	latexmk -CA

clean_all: clean
	rm -f */*.eps
	rm -f */*.pdf
	rm -f */targets.d
	rm -f */.ran-report-data

#### .pdf extra dependencies (mainly plots)
sim-realism.pdf: scenario1-send-recv/VT-0.5-vs-ideal-vs-fitted-fig.eps \
		 scenario1-send-recv/VT-0.98-vs-ideal-vs-fitted-fig.eps \
		 scenario1-big-votes/VT-0.5-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes/VT-0.98-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes-send-recv/VT-0.5-vs-ideal-4-hops-fig.eps \
		 scenario1-big-votes-send-recv/VT-0.98-vs-ideal-4-hops-fig.eps \
		 scenario6/IB-0.5-oldest-vs-freshest.eps \
		 scenario6/IB-0.6-oldest-vs-freshest.eps \
		 scenario6/IB-0.7-oldest-vs-freshest.eps \
		 scenario6/IB-0.8-oldest-vs-freshest.eps \
		 scenario6/IB-0.9-oldest-vs-freshest.eps \
		 scenario6/IB-0.98-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.5-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.6-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.7-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.8-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.9-oldest-vs-freshest.eps \
		 scenario6-10-cpus/IB-0.98-oldest-vs-freshest.eps \

## These plots we need for each main scenario.
MAIN_SCENARIOS := scenario1 scenario2 scenario3 scenario4 scenario5 scenario6
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

OTHER_SCENARIOS := scenario4-higher-IB-rate scenario4-lower-stage-length scenario4-best-IB-rate scenario4-20IB-small scenario4-higher-IB-rate-send-recv scenario4-higher-IB-rate-send-recv-short-stage scenario4-higher-IB-rate-send-recv-short-stage-no-cert scenario4-100-cpu scenario4-higher-IB-rate-send-recv-short-stage-no-cert-100-cpu scenario5-10-cpus

$(foreach s,$(OTHER_SCENARIOS),$(eval $(call main_scenario_template,$(s))))

#### Running simulations.

GIT_REV := $(shell git rev-parse HEAD)

ifeq ($(shell git status --porcelain --untracked-files=no),)
	GIT_DIRTY_TRACKED :=
else
	GIT_DIRTY_TRACKED := -$(shell git stash create)
endif

## In some cases it's useful to generate logs.
LOG_VERBOSITY ?= 0
SEED ?= 0
TAGGED_SIM_DATA = $(basename $@)-$(GIT_REV)$(GIT_DIRTY_TRACKED).json
SHORT_LEIOS = cabal run ols -- sim --output-seconds="$(SIM_SECONDS)" --output-file="$(TAGGED_SIM_DATA)" short-leios --seed $(SEED) --log-verbosity="$(LOG_VERBOSITY)"

%/sim-data.json: %/config.yaml %/topology.yaml
	$(SHORT_LEIOS) -l "$(word 1, $^)" -t "$(word 2, $^)" +RTS -s
	ln -srf $(TAGGED_SIM_DATA) $@
	ln -srf $(basename $(TAGGED_SIM_DATA)).log $(basename $@).log

%/sim-data.json: SIM_SECONDS=300

all_sims: $(shell ls */report-config.yaml | sed -e's/report-config.yaml/sim-data.json/')


#### Extracting diffusion data as .csv files.

SCENARIOS := $(shell ls */report-config.yaml | sed -e's/report-config.yaml//')

## This target is used so report-data is run only once, generating all the .csv.
%/.ran-report-data: %/report-config.yaml %/sim-data.json
	cabal run ols -- report-data -o "$(dir $@)" -c $^
	touch "$@"

## No need to rerun if missing.
.INTERMEDIATE: $(foreach s,$(SCENARIOS),$(s).ran-report-data)
## Do not want to rerun if missing, but should keep it.
.SECONDARY: $(foreach s,$(SCENARIOS),$(s)sim-data.json)

## The list of .csv to build is generated dinamically, based on
## report-config.yaml in the scenario directory.
## The list is cached as a rule in the targets.d files.
define scenario_csvs_template =
$(1) : $(2)/.ran-report-data
endef
%/targets.d : %/report-config.yaml
	@echo '$(call scenario_csvs_template,$(shell cabal run -v0 ols -- report-data -o $* -c $*/report-config.yaml --print-targets-only dummy),$*)' > $@

include $(foreach s,$(SCENARIOS),$(s)targets.d)

#### Plots
CDFSSCRIPT = ../gnuplot/latency_cdfs.gp
## GNUPLOT scripts take only 9 command line arguments, so for more
## than 4 cdfs in a graph we will need some other script.
CDFSPLOT = gnuplot -e "set terminal postscript eps enhanced color; set output '$@'" -c $(CDFSSCRIPT)

%-vs-ideal-fig.eps: $(CDFSSCRIPT) %.csv %-ideal.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal.csv" ideal

%-vs-ideal-vs-fitted-fig.eps: $(CDFSSCRIPT) %.csv %-ideal.csv %-ideal-fitted.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal.csv" ideal "$*-ideal-fitted.csv" ideal-fitted

%-vs-ideal-4-hops-fig.eps: $(CDFSSCRIPT) %.csv %-ideal-4-hops.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$*.csv" simulation "$*-ideal-4-hops.csv" ideal-4-hops

scenario6/%-oldest-vs-freshest.eps: $(CDFSSCRIPT) scenario6-freshest-first/%.csv scenario6/%.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$(word 2, $^)" freshest-first "$(word 3, $^)" oldest-first

scenario6-10-cpus/%-oldest-vs-freshest.eps: $(CDFSSCRIPT) scenario6-freshest-first-10-cpus/%.csv scenario6-10-cpus/%.csv
	$(CDFSPLOT) "$(notdir $*)" "Diffusion latency, s" "$(word 2, $^)" freshest-first "$(word 3, $^)" oldest-first
