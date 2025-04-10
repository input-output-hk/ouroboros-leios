all: config.schema.json topology.schema.json trace.haskell.schema.json trace.rust.schema.json

config.schema.json: config.d.ts
	npx typescript-json-schema config.d.ts Config > config.schema.json
	npx prettier -w config.schema.json

topology.schema.json: topology.d.ts
	npx typescript-json-schema topology.d.ts Topology > topology.schema.json
	npx prettier -w topology.schema.json

TRACE_SCHEMA_OPTS := --required --strictNullChecks

trace.haskell.schema.json: trace.haskell.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) trace.haskell.d.ts HaskellTraceEvent > trace.haskell.schema.json
	npx prettier -w trace.haskell.schema.json

trace.rust.schema.json: trace.rust.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) trace.rust.d.ts RustTraceEvent > trace.rust.schema.json
	npx prettier -w trace.rust.schema.json

%.array.schema.json: %.d.ts
	npx typescript-json-schema $(TRACE_SCHEMA_OPTS) $< TraceEvents > $@


%.trace.json: %.jsonl
	jq -cs '.' $< > $@

.PHONY: validate
validate: validate-config validate-topology validate-rust-trace validate-haskell-trace

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
validate-rust-trace: all example.rust.trace.json trace.rust.array.schema.json
	@echo "Validating Rust trace events..."
	@npx pajv -m schema.schema.json -s trace.rust.array.schema.json -d example.rust.trace.json && echo "example.rust.jsonl valid"
