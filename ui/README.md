# Leios visualization UI

User interface to display Leios traffic in traces produced by simulations,
prototypes and node implementations.

## Getting started

Example traces are available via Git LFS. Fetch them first:

```bash
git lfs fetch
git lfs checkout
```

Install dependencies and build the project with:

```bash
npm install
npm run build
```

Or run the development server with:

```bash
npm start
```

## Add a scenario from sim-rs

To prepare a scenario to visualize, find or add the topology to the public directory, for example:

```sh
mkdir -p public/topologies
ln -sr ../sim-rs/test_data/small.yaml public/topologies/small.yaml
```

And generate a trace to visualize using the built `sim-rs`, for example using the CIP scenario:

```bash
mkdir -p public/traces
cat ../analysis/sims/cip/experiments/NA,0.200/config.yaml \
  | jq '."tx-start-time" = 20' > public/traces/config-200txkbs.json
../sim-rs/target/release/sim-cli -p public/traces/config-200txkbs.json public/topologies/small.yaml public/traces/small-200txkbs.jsonl -s 120
```

You might want to filter out `Cpu` events (not visualized) and, in case you want to store it, use gzip and git lfs:

```bash
grep -v 'Cpu' < public/traces/small-200txkbs.jsonl > public/traces/small-200txkbs-nocpu.jsonl
gzip public/traces/small-200txkbs-nocpu.jsonl
git lfs track public/traces/small-200txkbs-nocpu.jsonl.gz
```

Then update `public/scenarios.json` accordingly:

```json
{
  "scenarios": [
    {
      "name": "200 TxkB/s",
      "topology": "topologies/small.yaml",
      "duration": 120,
      "trace": "traces/small-200txkbs-nocpu.jsonl.gz"
    }
  ]
}
```

## Add a live Loki streaming scenario

For live visualization of node logs, you can configure scenarios that connect to a Loki instance via WebSocket. This allows real-time monitoring of running Cardano nodes.

First, ensure your Loki instance is running and accessible, for example by following the [leios-demo](https://github.com/input-output-hk/leios-demo/) instructions.
Then add a scenario with a `loki` field instead of `trace` to `public/scenarios.json`:

```json
{
  "scenarios": [
    {
      "name": "Leios Demo 202511",
      "topology": "topologies/prototype.yaml",
      "duration": 300,
      "loki": "localhost:3100"
    }
  ]
}
```

## Configuration

Scenarios support two modes:

- **Stored traces**: Use the `trace` field pointing to a JSONL file (optionally gzipped)
- **Live streaming**: Use the `loki` field with host:port of your Loki instance

Both modes require a `topology` field specifying the network topology YAML file and a `duration` defining the amount of loaded data.
