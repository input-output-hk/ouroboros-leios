# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Leios Visualization UI — a React/TypeScript web app for visualizing network traffic from Leios protocol simulations. Displays animated network graphs from either precomputed JSONL traces (from the sibling `sim-rs/` Rust simulator) or live Loki WebSocket streams.

## Build & Dev Commands

```bash
npm install          # Install dependencies
npm start            # Dev server on port 3000 (alias: npm run dev)
npm run build        # TypeScript check + Vite production build
npm run lint         # ESLint
npm run preview      # Preview production build
nix run .#ui-live    # Build and serve via Nix
```

Nix devshell: `use flake .#dev-ui` (via `.envrc`/direnv).

## Architecture

**Stack**: React 19, TypeScript (strict), Vite, Tailwind CSS 4

**State management**: React Context + useReducer (`src/contexts/SimContext/`). The reducer handles all state transitions — scenario loading, topology, event batches, playback controls, canvas state, and Loki connection status.

**Key modules**:
- `src/components/Sim/` — Scenario selection, playback controls, timeline. Trace loading uses a **Web Worker** (`hooks/worker.ts`) to parse JSONL without blocking the UI.
- `src/components/Graph/` — HTML **Canvas**-based network topology rendering with animated message arcs between nodes.
- `src/contexts/SimContext/` — Centralized state: `context.ts` (defaults), `types.ts` (state/action types), `reducer.ts` (state transitions).

**Data flow**: Scenario selected → topology YAML fetched & parsed → trace loaded via Web Worker (or Loki WebSocket connected) → events dispatched in batches → playback loop aggregates visible events at 60 FPS → Canvas renders nodes, links, and in-flight messages.

**Two data modes**:
- Stored traces: JSONL/JSONL.gz files in `public/traces/`, parsed by Web Worker
- Live streaming: WebSocket to Loki instance (`src/components/Sim/hooks/useLokiWebSocket.ts`)

**Message types**: TransactionGenerated/Received/Sent, EBGenerated/Received/Sent, RBGenerated/Received/Sent, VTBundleGenerated/Received/Sent — each color-coded (green/blue/red/cyan).

## Configuration

- `public/scenarios.json` — scenario definitions (name, topology path, duration, trace path or loki host)
- `public/topologies/*.yaml` — network topology files (symlinked from `data/simulation/`)
- Path alias: `@/*` maps to `./src/*`
- Vite base path: `/visualizer/`
