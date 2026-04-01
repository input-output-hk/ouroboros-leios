# net-ui

Real-time web UI for visualizing `net-cluster` test networks. Built with React, Vite, Material-UI, and D3.

## Features

- Force-directed topology graph showing nodes and peer connections
- Per-node status indicators (slot, tip, block production)
- Chain tree view showing forks and block propagation across nodes
- Aggregate charts (block rates, bandwidth, latency) via Recharts
- Scrollable event log with collapsible blur overlay
- Inspector panel for node and edge details
- Polls cluster HTTP API for live updates

## Structure

```
src/
├── main.tsx              # React entry point, MUI theme setup
├── App.tsx               # Main app layout, polling orchestration
├── api.ts                # HTTP client for cluster API
├── store.ts              # Zustand state management
├── types.ts              # TypeScript type definitions
├── theme.ts              # Material-UI theme configuration
├── components/
│   ├── TopologyGraph.tsx  # Force-directed network graph (D3)
│   ├── TopologyNode.tsx   # Individual node rendering
│   ├── TopologyEdge.tsx   # Edge rendering with latency labels
│   ├── ChainTreeView.tsx  # Block chain tree visualization
│   ├── AggregateCharts.tsx # Metrics charts (Recharts)
│   ├── InspectorPanel.tsx # Node/edge detail panel
│   └── EventLog.tsx       # Event history display
└── hooks/
    ├── usePolling.ts      # Periodic data fetching
    ├── useForceLayout.ts  # D3 force simulation management
    └── useEventStream.ts  # Real-time event streaming
```

## Usage

```sh
# Install dependencies:
cd net-ui && npm install

# Start dev server (connects to cluster on localhost):
npm run dev

# Build for production:
npm run build
```

## Dependencies

| Package | Purpose |
|---------|---------|
| React 19 | UI framework |
| Material-UI 6 | Component library |
| D3 Force | Force-directed graph layout |
| Recharts | Chart visualizations |
| Zustand | State management |
| Vite | Build tool and dev server |
