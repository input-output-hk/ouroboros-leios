# Leios Topology Viewer

Interactive web visualization of the v4 mainnet topology that lives in
`data/simulation/pseudo-mainnet/`.

## What you see

- **Node clusters** — one circle marker per Cardano stake pool at its real
  geographic location, grouped into traffic-light cluster bubbles
  (green / yellow / orange / red by member count) via
  Leaflet.markercluster.  Single (unclustered) nodes are coloured by
  their provider (AWS amber, GCP blue, Hetzner red, OVH purple, …) and
  sized by stake.
- **Corridor lines** — aggregated edges between countries, providers, or
  continents (toggle in the left panel), drawn as straight lines between
  group centroids.  Line width is `log(edge count)`, line colour is mean
  latency (green → red).

## Prerequisites

- **Node.js ≥ 18** (any modern LTS), npm
- **uv** for the Python preprocessor (`brew install uv` on macOS, or
  `curl -LsSf https://astral.sh/uv/install.sh | sh`).  Only needed if you
  want to *regenerate* the JSON data; the prebuilt JSON in
  `public/data/` ships with the repo.

## How to run

### 1. Install JS dependencies (once)

```bash
cd topology-viewer
npm install        # ~20s; installs React, Leaflet, Leaflet.markercluster, Tailwind
```

### 2. (Optional) Regenerate the topology JSON data

```bash
npm run preprocess
```

This runs `scripts/build-viewer-data.py` over
`../data/simulation/pseudo-mainnet/topology-v4-{mini,mainnet}.yaml`
and writes compact JSON to `public/data/`.  Only re-run when you
regenerate the topology YAMLs.

### 3. Dev server (with hot-reload)

```bash
npm run dev
```

Opens at **http://localhost:5173**.  Edits to `src/**` reload instantly.

### 4. Production build

```bash
npm run build      # outputs topology-viewer/dist/  (~3 MB total)
npm run preview    # serve dist/ on http://localhost:5174
```

`topology-viewer/dist/` is a self-contained static site — drop it into any static
host (GitHub Pages, S3, Netlify, `python3 -m http.server`).  No
backend, no API keys, no external services apart from the OpenStreetMap
tile servers.

### Troubleshooting

| Symptom | Fix |
|---|---|
| `Failed to load index.json` on first launch | Run `npm run preprocess` to generate `public/data/*.json` |
| Map tiles don't appear | OpenStreetMap tile server unreachable; check network or replace `L.tileLayer(...)` URL in `src/components/MapView.tsx` with another tile provider |
| Build fails with peer-dep warnings | Safe to ignore; if it fails hard, delete `node_modules/` and `package-lock.json` then `npm install` again |
| Panels appear *behind* the map | z-index issue with Leaflet's panes — check `src/styles.css` overrides for `.leaflet-container` / `.leaflet-pane` |

## What's inside

```
topology-viewer/
├── scripts/build-viewer-data.py     # YAML → compact JSON preprocessor
├── public/data/                     # generated JSON (one per topology)
│   ├── index.json
│   └── topology-v4-{mini,mainnet}.json
├── src/
│   ├── App.tsx                       layout
│   ├── components/
│   │   ├── MapView.tsx               Leaflet + markercluster integration
│   │   ├── ControlPanel.tsx          topology selector, layer toggles
│   │   ├── LegendPanel.tsx           provider palette, drop-toggle
│   │   └── HoverTooltip.tsx          per-node detail card
│   ├── data/                         loader + types
│   ├── state/useViewerState.ts       Zustand store
│   ├── utils/colors.ts               provider palette, latency gradient
│   └── styles.css                    Tailwind + Leaflet override
└── ...
```

## Stack

- **React 18 + TypeScript** UI
- **Vite** build
- **Leaflet 1.9** + **Leaflet.markercluster 1.5** — map rendering and clustering
- **OpenStreetMap raster tiles** (no API key required)
- **Tailwind CSS** styling
- **Zustand** state
- **Python preprocessor** (uv-script) that compacts the topology YAMLs to ≤1 MB JSON each

## Available topologies

Use the topology dropdown to swap between:

| Variant | Nodes | Edges | Edge model |
|---|---:|---:|---|
| v4-mini | 250 | 8.5k | **Hybrid per-pool** — top-250 stake |
| v4-mainnet | 2,685 | 95k | **Hybrid per-pool** — every active Cardano pool, one node each |

## Failure-scenario simulation

Click any provider in the right-hand legend to **drop** it from rendering.
Node markers disappear and corridor lines recompute.  Try:

- Drop **AWS** → 22.7% of stake offline; cross-Atlantic corridors shrink
- Drop **OVH** + **Hetzner** → severe European fragmentation
- Drop all hyperscalers (AWS + GCP + Azure) → 41.75% of stake gone (the
  joint-failure scenario in `mpo_topology_failure_scenarios.csv`)

Click "Restore all" at the bottom of the control panel to re-enable.

## Regenerating data

Whenever you regenerate the topology YAMLs:

```bash
cd topology-viewer
npm run preprocess
```

This re-reads `../data/simulation/pseudo-mainnet/topology-v4-*.yaml` and
overwrites `public/data/*.json`.
