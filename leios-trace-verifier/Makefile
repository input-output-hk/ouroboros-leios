# Constants
AGDA?=agda
AGDA_RUN=$(AGDA) --transliterate
OUT_DIR?=dist
HS_DIR=$(OUT_DIR)/haskell
MALONZO_DIR=MAlonzo/Code
CABAL_TEST=cabal run test

# Agda -> Haskell
define agdaToHs
    @echo "Generating $@"
    $(eval CABAL_FILE=trace-parser.cabal)
    $(eval HS_DIST=$(HS_DIR)/src)
    mkdir -p $(HS_DIST)
    cp -r hs-src/* $(HS_DIR)/
    cp hs-src/$(CABAL_FILE) $(HS_DIR)/
    mkdir -p $(HS_DIR)/data
    cp -r conformance-traces/{config.yaml,topology.yaml,topologies,valid,invalid} $(HS_DIR)/data/
    $(AGDA_RUN) -c --ghc-dont-call-ghc --compile-dir $(HS_DIST) $<
    find $(HS_DIST)/MAlonzo -name "*.hs" -print\
      | sed "s#^$(HS_DIST)/#        #;s#\.hs##;s#/#.#g"\
      >> $(HS_DIR)/$(CABAL_FILE)
endef
HS_LEIOS=$(HS_DIST)/$(MALONZO_DIR)/trace-parser.hs

all: $(HS_LEIOS)
	cabal build all

clean:
	rm -rf _build dist dist-newstyle

$(HS_LEIOS): src/trace-parser.agda
	$(call agdaToHs,trace-parser)

# Leios.Base.Praos (see docs/praos-base-machine-sketch.md), checked one module
# at a time.  Praos.agda is --safe; Instance.agda isn't (Praos's
# chainFromBlock is TERMINATING).
.PHONY: praos-base praos-instance praos-assumptions praos-machine
praos-base:
	$(AGDA) src/Leios/Base/Praos.agda

praos-instance:
	$(AGDA) src/Leios/Base/Praos/Instance.agda

praos-assumptions:
	$(AGDA) src/Leios/Base/Praos/Assumptions.agda

praos-machine:
	$(AGDA) src/Leios/Base/Praos/Machine.agda

# The validation functionality (src/Leios/Ledger/Validation*).  The machine
# and its backend from a decidable transition system are part of the
# verifier's build.  The Dijkstra-backed instance needs the formal-ledger
# library (formal-ledger-specifications), which the verifier's build does
# not have: LEDGER_LIBRARIES names a libraries file that lists it next to
# the verifier's dependencies.
LEDGER_LIBRARIES?=
LEDGER_LIBS=standard-library standard-library-classes standard-library-meta \
  abstract-set-theory iog-prelude categorical-crypto leios-spec formal-ledger
.PHONY: validation ledger-validation
validation:
	$(AGDA) src/Leios/Ledger/Validation/STS.agda

ledger-validation:
	$(AGDA) --library-file=$(LEDGER_LIBRARIES) $(addprefix -l ,$(LEDGER_LIBS)) -i src \
	  src/Leios/Ledger/Validation/Dijkstra.agda
