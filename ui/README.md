# Leios visualization UI

User interface to display Leios traffic in traces produced by simulations,
prototypes and node implementations.

## Getting started

Example traces are available via Git LFS. Fetch them first:

``` bash
git lfs fetch
git lfs checkout
```

Install dependencies and build the project with:

``` bash
npm install
npm run build
```

Or run the development server with:

``` bash
npm start
```

## Add a scenario from sim-rs

To prepare a scenario to visualize, add or update `public/scenarios.json`:

```json
{
  "scenarios": [
    {
      "name": "My Scenario",
      "topology": "topologies/thousand.yaml",
      "duration": 30.0,
      "trace": "traces/myscenario.jsonl"
    }
  ]
}
```

Now add that topology to the public directory:

```sh
mkdir -p public/topologies
cp ../sim-rs/test-data/thousand.yaml public/topologies
```

And generate a trace to visualize from the `sim-rs` directory:

```bash
mkdir -p ../ui/public/traces
cargo run --release test_data/thousand.yaml ../ui/public/traces/myscenario.jsonl -s 30
```
