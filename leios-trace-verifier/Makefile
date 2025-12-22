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
    cp -r conformance-traces/{config.yaml,topology.yaml,valid,invalid} $(HS_DIR)/data/
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
