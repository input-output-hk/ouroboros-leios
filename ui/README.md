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

To prepare a scenario to visualize, add or update `public/scenarios.json`:

```json
{
  "scenarios": [
    {
      "name": "Example",
      "topology": "topologies/example.yaml",
      "duration": 300,
      "trace": "traces/example.jsonl",
      "aggregated": false
    }
  ]
}
```

Now add that topology to the public directory, for example:

```sh
mkdir -p public/topologies
ln -sr ../sim-rs/test_data/small.yaml public/topologies/example.yaml
```

And generate a trace to visualize using the built `sim-rs`:

```bash
mkdir -p public/traces
../sim-rs/target/release/sim-cli -p ../analysis/sims/cip/experiments/NA,0.200/config.yaml public/topologies/example.yaml public/traces/example.jsonl -s 120
```

In case you want to store it, use gzip and git lfs:

```bash
gzip public/traces/examples.jsonl
git lfs track public/traces/examples.jsonl.gz
```
