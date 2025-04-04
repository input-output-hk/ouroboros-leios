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
validate: all
	@echo "Validating config..."
	@npx pajv -m schema.schema.json -s config.schema.json -d config.default.yaml > /dev/null && echo "config.default.yaml valid" || exit 1
	@echo "Validating topology..."
	@npx pajv -m schema.schema.json -s topology.schema.json -d topology-dense-52.yaml > /dev/null && echo "topology-dense-52.yaml valid" || exit 1
	@echo "Validating Haskell trace events..."
	@line_num=0; \
	while IFS= read -r line; do \
		line_num=$$((line_num + 1)); \
		echo "$$line" > temp.json; \
		if ! npx ajv-cli validate -s trace.haskell.schema.json -d temp.json 2>/dev/null >/dev/null; then \
			echo "Error in example.haskell.jsonl at line $$line_num:"; \
			echo "$$line"; \
			npx ajv-cli validate -s trace.haskell.schema.json -d temp.json; \
			rm -f temp.json; \
			exit 1; \
		fi; \
	done < example.haskell.jsonl && echo "example.haskell.jsonl valid"
	@echo "Validating Rust trace events..."
	@line_num=0; \
	while IFS= read -r line; do \
		line_num=$$((line_num + 1)); \
		echo "$$line" > temp.json; \
		if ! npx ajv-cli validate -s trace.rust.schema.json -d temp.json 2>/dev/null >/dev/null; then \
			echo "Error in example.rust.jsonl at line $$line_num:"; \
			echo "$$line"; \
			npx ajv-cli validate -s trace.rust.schema.json -d temp.json; \
			rm -f temp.json; \
			exit 1; \
		fi; \
	done < example.rust.jsonl && echo "example.rust.jsonl valid"
	@rm -f temp.json
