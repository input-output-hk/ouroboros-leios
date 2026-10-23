# input.json format

This file documents `input.json`, the single source of truth for the topology-plus-schedule passed to the simulator.
`run_and_plot.sh` produces it by merging a `inputfiles/topo-*.json` (topology) and a `inputfiles/schedule-*.json` (schedule) with `jq`; `mininet_topo.py` reads it; the plot scripts read it for annotations.

## Top-level structure

```
{
  "nic_bw_mbit": ...,
  "default_duration": ...,
  "edges": [ ... ],
  "tuned_initcwnd": [ ... ],
  "node_nicknames": { ... },
  "schedule": [ ... ]
}
```

`edges`, `tuned_initcwnd`, `node_nicknames`, `nic_bw_mbit`, and `default_duration` come from the topology file.
`schedule` comes from the schedule file.

## Global parameters

- **`nic_bw_mbit`**: end-host NIC capacity in Mbit/s.
  Present for backward compatibility with the pre-middlebox topology; the middlebox architecture ignores it in favour of per-edge `bw_mbit`.
- **`default_duration`**: simulation duration in seconds, overridable via `--duration`.
- **`tuned_initcwnd`**: list of node IDs whose operators have raised their kernel TCP defaults (`initcwnd=200`, `initrwnd=200` on per-peer routes).
  Untuned nodes use Linux defaults.
- **`node_nicknames`**: display names for each node ID, used in plots and `topology.png`.
  Keys are stringified node IDs (JSON doesn't allow integer keys).

## Edges

The `edges` array describes the graph.
Each entry has:

- **`a`, `b`**: node IDs (convention: `a < b`).
- **`bw_mbit`**: link bandwidth in Mbit/s.
- **`delay`**: one-way base latency (string, e.g. `"50ms"`).
- **`jitter`**: jitter magnitude (string, e.g. `"5ms"`). Applied with paretonormal distribution at 25% correlation.
- **`loss_gemodel`**: Gilbert-Elliott 4-state Markov loss `[p, r, 1-h, 1-k]` or `null`.
  - `p` = good-to-bad transition probability.
  - `r` = bad-to-good recovery probability.
  - `1-h` = loss rate in bad state.
  - `1-k` = loss rate in good state.
  - Split across the two propagation legs (host→middlebox and middlebox→host), so each leg applies `p/2`.
- **`a_pulls`, `b_pulls`**: which endpoint initiates the pull direction. Used for the arrowhead direction in `topology.png`; traffic shaping itself is symmetric.

See NOTES.md for how these map onto the per-link middlebox + tc chain (`netem` on the host side, `htb + fq_codel` on the middlebox egress).

## Schedule

The `schedule` array defines when each payload is injected and at which node(s).
Each entry has:

- **`nickname`**: display name for the payload.
- **`components`**: array of component sizes in bytes (each between 30 and 16384).
  The array length determines the number of components; the sum determines total payload size.
- **`time`** and **`node`**: either both scalars (a single injection) or both arrays of equal non-zero length (the same payload co-injected at several `(time, node)` pairs).
  Array form is used to simulate a payload reaching multiple nodes via an upstream path the topology doesn't explicitly model.

Every node reads the full schedule and filters by its own `--id`.
Nodes not listed in any injection never inject payloads but still participate in diffusion.

### Example: single injection

```json
{
  "time": 5,
  "node": 1,
  "nickname": "payload-1",
  "components": [4096, 8192, ...]
}
```

### Example: co-injection

```json
{
  "time": [5, 5, 5, 5, 5, 5, 5, 5],
  "node": [1, 2, 3, 4, 5, 6, 7, 8],
  "nickname": "payload-1",
  "components": [4096, 8192, ...]
}
```

All 8 nodes inject the same payload (identical component list → identical manifest hash) at the same time.
Same-hash injections at different times simulate staggered arrivals from an implicit upstream path.
