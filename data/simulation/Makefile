all: config.schema.json topology.schema.json trace.haskell.schema.json trace.rust.schema.json

config.schema.json: config.d.ts
	npx typescript-json-schema config.d.ts Config > config.schema.json
	npx prettier -w config.schema.json

topology.schema.json: topology.d.ts
	npx typescript-json-schema topology.d.ts Topology > topology.schema.json
	npx prettier -w topology.schema.json

trace.haskell.schema.json: trace.haskell.d.ts
	npx typescript-json-schema trace.haskell.d.ts HaskellTraceEvent > trace.haskell.schema.json
	npx prettier -w trace.haskell.schema.json

trace.rust.schema.json: trace.rust.d.ts
	npx typescript-json-schema trace.rust.d.ts RustTraceEvent > trace.rust.schema.json
	npx prettier -w trace.rust.schema.json

.PHONY: validate
validate:
	npx pajv -m schema.schema.json -s config.schema.json -d config.default.yaml
	npx pajv -m schema.schema.json -s topology.schema.json -d topology-dense-52.yaml
	npx pajv -m schema.schema.json -s trace.haskell.schema.json -d example.haskell.jsonl
	npx pajv -m schema.schema.json -s trace.rust.schema.json -d example.rust.jsonl
