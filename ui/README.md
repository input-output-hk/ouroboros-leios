# Leios visualization UI

User interface to display Leios traffic in traces produced by simulations,
prototypes and node implementations.

## Getting started

Install dependencies and build the project with:

```bash
npm install
npm run build
```

Or run the development server with:

```bash
npm start
```

Or build & start the ui using nix:

``` bash
nix run .#ui-live
```

## Add a scenario from sim-rs

The Rust Leios simulator (`sim-rs`) and a few baseline topologies (`small.yaml`,
`thousand.yaml`) now live in [cardano-scaling/leios-tools](https://github.com/cardano-scaling/leios-tools).
Bundled topologies in `public/topologies/` are kept here directly.

To add a new topology, drop the YAML file in `public/topologies/`. Then generate
a trace to visualize with a build of `sim-rs` from the leios-tools repo, for
example using the CIP scenario:

```bash
mkdir -p public/traces
cat ../analysis/sims/cip/experiments/NA,0.200/config.yaml \
  | jq '."tx-start-time" = 20' > public/traces/config-200txkbs.json
/path/to/leios-tools/sim-rs/target/release/sim-cli \
  -p public/traces/config-200txkbs.json \
  public/topologies/small.yaml \
  public/traces/small-200txkbs.jsonl -s 120
```

You might want to filter out `Cpu` events (not visualized) and compress the trace:

```bash
grep -v 'Cpu' < public/traces/small-200txkbs.jsonl > public/traces/small-200txkbs-nocpu.jsonl
gzip public/traces/small-200txkbs-nocpu.jsonl
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

### Auto-starting scenarios

Scenarios can be auto-loaded/-connected using a URL query parameter:

```
?scenario=<index>
```

Where `<index>` is the zero-based index of the scenario in the scenarios.json array. For example:

- `?scenario=0` - Auto-loads the first scenario (e.g., "200 TxkB/s")
- `?scenario=1` - Auto-loads the second scenario (e.g., "1 TxkB/s")
- `?scenario=2` - Auto-connects to the third scenario (e.g., "Leios Demo 202511")

This is useful for direct links, bookmarking, or embedding specific scenarios.
