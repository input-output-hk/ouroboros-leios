import { create } from "zustand";
import type {
  Topology,
  StatsSnapshot,
  OutputEvent,
  AggregatePoint,
  NodeSeriesPoint,
} from "./types";
import { fetchTopology, fetchAllStats, fetchEvents } from "./api";

const MAX_SERIES = 300;
const MAX_EVENTS = 500;

export interface DashboardState {
  // Topology (loaded once)
  topology: Topology | null;
  nodePositions: Record<string, { x: number; y: number }>;
  layoutReady: boolean;
  loadTopology: () => Promise<void>;
  setNodePosition: (id: string, pos: { x: number; y: number }) => void;
  setNodePositions: (positions: Record<string, { x: number; y: number }>) => void;

  // Stats (polled 1s)
  latestStats: Record<string, StatsSnapshot>;
  aggregateSeries: AggregatePoint[];
  nodeTimeSeries: Record<string, NodeSeriesPoint[]>;
  pollStats: () => Promise<void>;

  // Events (polled 1s)
  events: OutputEvent[];
  lastEventTime: number;
  pollEvents: () => Promise<void>;

  // Selection
  selectedNodeId: string | null;
  selectedEdge: { from: number; to: number } | null;
  selectNode: (id: string | null) => void;
  selectEdge: (edge: { from: number; to: number } | null) => void;
}

export const useStore = create<DashboardState>()((set, get) => ({
  // --- Topology ---
  topology: null,
  nodePositions: {},
  layoutReady: false,

  loadTopology: async () => {
    try {
      const topology = await fetchTopology();
      set({ topology });
    } catch (e) {
      console.error("Failed to load topology:", e);
    }
  },

  setNodePosition: (id, pos) =>
    set((s) => ({
      nodePositions: { ...s.nodePositions, [id]: pos },
    })),

  setNodePositions: (positions) =>
    set({ nodePositions: positions, layoutReady: true }),

  // --- Stats ---
  latestStats: {},
  aggregateSeries: [],
  nodeTimeSeries: {},

  pollStats: async () => {
    try {
      const stats = await fetchAllStats();
      const now = Date.now();

      let totalBandwidth = 0;
      let totalMessages = 0;
      let totalBlocks = 0;
      const newNodeSeries: Record<string, NodeSeriesPoint[]> = {
        ...get().nodeTimeSeries,
      };

      for (const snap of Object.values(stats)) {
        let nodeBw = 0;
        for (const p of snap.peers) {
          nodeBw += p.bytes_sent + p.bytes_received;
        }
        totalBandwidth += nodeBw;
        totalMessages +=
          snap.blocks_produced + snap.blocks_received + snap.txs_generated;
        totalBlocks += snap.blocks_produced;

        const prev = newNodeSeries[snap.node_id] ?? [];
        const updated = [
          ...prev,
          {
            time: now,
            bandwidth: nodeBw,
            messages:
              snap.blocks_produced + snap.blocks_received + snap.txs_generated,
          },
        ].slice(-MAX_SERIES);
        newNodeSeries[snap.node_id] = updated;
      }

      const point: AggregatePoint = {
        time: now,
        bandwidth: totalBandwidth,
        messages: totalMessages,
        blocks: totalBlocks,
      };

      set((s) => ({
        latestStats: stats,
        aggregateSeries: [...s.aggregateSeries, point].slice(-MAX_SERIES),
        nodeTimeSeries: newNodeSeries,
      }));
    } catch (e) {
      console.error("Failed to poll stats:", e);
    }
  },

  // --- Events ---
  events: [],
  lastEventTime: 0,

  pollEvents: async () => {
    try {
      const { lastEventTime } = get();
      const newEvents = await fetchEvents(lastEventTime);
      if (newEvents.length === 0) return;

      const maxTime = newEvents.reduce(
        (max, e) => Math.max(max, e.time_s),
        lastEventTime,
      );

      set((s) => ({
        events: [...s.events, ...newEvents].slice(-MAX_EVENTS),
        lastEventTime: maxTime,
      }));
    } catch (e) {
      console.error("Failed to poll events:", e);
    }
  },

  // --- Selection ---
  selectedNodeId: null,
  selectedEdge: null,

  selectNode: (id) => set({ selectedNodeId: id, selectedEdge: null }),
  selectEdge: (edge) => set({ selectedEdge: edge, selectedNodeId: null }),
}));
