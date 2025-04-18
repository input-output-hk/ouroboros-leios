all: config.schema.json topology.schema.json trace.haskell.schema.json trace.rust.schema.json trace.shared.schema.json

config.schema.json: config.d.ts
	npx typescript-json-schema config.d.ts Config > config.schema.json
	npx prettier -w config.schema.json

topology.schema.json: topology.d.ts
	npx typescript-json-schema topology.d.ts Topology > topology.schema.json
	npx prettier -w topology.schema.json

TRACE_SCHEMA_OPTS := --required --strictNullChecks

trace.shared.schema.json: trace.shared.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) $< TraceEvent > $@
	npx prettier -w $@

trace.haskell.schema.json: trace.haskell.d.ts trace.shared.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) trace.haskell.d.ts HaskellTraceEvent > trace.haskell.schema.json
	npx prettier -w trace.haskell.schema.json

trace.rust.schema.json: trace.rust.d.ts trace.shared.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) trace.rust.d.ts RustTraceEvent > trace.rust.schema.json
	npx prettier -w trace.rust.schema.json

QUERY := '.definitions.UnknownType = {"type": "string", "not": $$k[0] }'

%.knowntype.schema.json: %.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) $< KnownType > $@
%.array.schema.json: %.d.ts %.knowntype.schema.json
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) $< TraceEvents | jq --slurpfile k $(word 2, $^) $(QUERY) > $@

%.trace.json: %.jsonl
	jq -cs '.' $< > $@

.PHONY: validate
validate: validate-config validate-topology validate-rust-trace validate-haskell-trace validate-rust-trace-against-shared validate-haskell-trace-against-shared

.PHONY: validate-config
validate-config: config.schema.json config.default.yaml
	@echo "Validating config..."
	@npx pajv -m schema.schema.json -s config.schema.json -d config.default.yaml

.PHONY: validate-topology
validate-topology: topology.schema.json topology-dense-52.yaml
	@echo "Validating topology..."
	@npx pajv -m schema.schema.json -s topology.schema.json -d topology-dense-52.yaml

.PHONY: validate-haskell-trace
validate-haskell-trace: example.haskell.trace.json trace.haskell.array.schema.json
	@echo "Validating Haskell trace events..."
	@npx ajv-cli validate -s trace.haskell.array.schema.json -d example.haskell.trace.json && echo "example.haskell.jsonl valid"

.PHONY: validate-rust-trace
validate-rust-trace: example.rust.trace.json trace.rust.array.schema.json
	@echo "Validating Rust trace events..."
	@npx pajv -m schema.schema.json -s trace.rust.array.schema.json -d example.rust.trace.json && echo "example.rust.jsonl valid"

.PHONY: validate-rust-trace-against-shared
validate-rust-trace-against-shared: example.rust.trace.json trace.shared.array.schema.json
	@echo "Validating Rust trace events against shared schema..."
	@npx pajv -m schema.schema.json -s $(word 2,$^) -d $(word 1,$^) && echo "example.rust.jsonl valid against shared schema."

.PHONY: validate-haskell-trace-against-shared
validate-haskell-trace-against-shared: example.haskell.trace.json trace.shared.array.schema.json
	@echo "Validating Haskell trace events against shared schema..."
	@npx pajv -m schema.schema.json -s $(word 2,$^) -d $(word 1,$^) && echo "example.haskell.jsonl valid against shared schema."
