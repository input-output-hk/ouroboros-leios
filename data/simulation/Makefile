all: config.schema.json topology.schema.json

config.schema.json: config.d.ts
	npx typescript-json-schema config.d.ts Config > config.schema.json

topology.schema.json: topology.d.ts
	npx typescript-json-schema topology.d.ts Topology > topology.schema.json

.PHONY: validate
validate:
	npx pajv -m schema.schema.json -s config.schema.json -d config.default.yaml
	npx pajv -m schema.schema.json -s topology.schema.json -d topology-dense-52.yaml
