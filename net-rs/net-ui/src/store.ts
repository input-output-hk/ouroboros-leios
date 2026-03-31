import { create } from "zustand";
import type {
  Topology,
  StatsSnapshot,
  OutputEvent,
  AggregatePoint,
  NodeSeriesPoint,
} from "./types";
import { fetchTopology, fetchAllStats, fetchEvents } from "./api";

const MAX_SERIES = 300; // ~5 min at 1s stats interval
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
  prevSnapshot: { time: number; bandwidth: number; messages: number; blocks: number } | null;
  prevNodeSnapshot: Record<string, { time: number; bandwidth: number; messages: number; blocks: number }>;
  aggregateSeries: AggregatePoint[];
  nodeTimeSeries: Record<string, NodeSeriesPoint[]>;
  pollStats: () => Promise<void>;

  // Events
  events: OutputEvent[];
  lastEventTime: number;
  eventsPaused: boolean;
  handleEventBatch: (events: OutputEvent[]) => void;
  pollEvents: () => Promise<void>;
  toggleEventsPause: () => void;

  // Node flash (block produced/received)
  nodeFlash: Record<string, "produced" | "received" | null>;

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
  prevSnapshot: null,
  prevNodeSnapshot: {},
  aggregateSeries: [],
  nodeTimeSeries: {},

  pollStats: async () => {
    try {
      const stats = await fetchAllStats();
      const now = Date.now();
      const { prevSnapshot, prevNodeSnapshot } = get();

      // Compute current cumulative totals
      let totalBandwidth = 0;
      let totalMessages = 0;
      let totalBlocks = 0;
      const curNodeCum: Record<string, { bandwidth: number; messages: number; blocks: number }> = {};

      for (const snap of Object.values(stats)) {
        let nodeBw = 0;
        for (const p of snap.peers) {
          nodeBw += p.bytes_sent + p.bytes_received;
        }
        totalBandwidth += nodeBw;
        totalMessages +=
          snap.blocks_produced + snap.blocks_received + snap.txs_generated;
        totalBlocks += snap.blocks_produced;

        curNodeCum[snap.node_id] = {
          bandwidth: nodeBw,
          messages:
            snap.blocks_produced + snap.blocks_received + snap.txs_generated,
          blocks: snap.blocks_produced,
        };
      }

      const curSnap = { time: now, bandwidth: totalBandwidth, messages: totalMessages, blocks: totalBlocks };

      if (prevSnapshot) {
        const changed =
          curSnap.bandwidth !== prevSnapshot.bandwidth ||
          curSnap.messages !== prevSnapshot.messages ||
          curSnap.blocks !== prevSnapshot.blocks;

        const newNodeSeries: Record<string, NodeSeriesPoint[]> = {
          ...get().nodeTimeSeries,
        };
        const newNodeSnap: Record<string, { time: number; bandwidth: number; messages: number; blocks: number }> = {
          ...prevNodeSnapshot,
        };

        if (changed) {
          const dtSec = Math.max(0.1, (now - prevSnapshot.time) / 1000);
          const point: AggregatePoint = {
            time: now,
            bandwidth: Math.max(0, curSnap.bandwidth - prevSnapshot.bandwidth) / dtSec,
            messages: Math.max(0, curSnap.messages - prevSnapshot.messages),
            blocks: Math.max(0, curSnap.blocks - prevSnapshot.blocks),
          };

          for (const [nodeId, cur] of Object.entries(curNodeCum)) {
            const prev = prevNodeSnapshot[nodeId];
            if (!prev) continue;
            const nodeChanged = cur.bandwidth !== prev.bandwidth || cur.messages !== prev.messages || cur.blocks !== prev.blocks;
            if (nodeChanged) {
              const nodeDt = Math.max(0.1, (now - prev.time) / 1000);
              const series = newNodeSeries[nodeId] ?? [];
              newNodeSeries[nodeId] = [
                ...series,
                {
                  time: now,
                  bandwidth: Math.max(0, cur.bandwidth - prev.bandwidth) / nodeDt,
                  messages: Math.max(0, cur.messages - prev.messages),
                  blocks: Math.max(0, cur.blocks - prev.blocks),
                },
              ].slice(-MAX_SERIES);
              newNodeSnap[nodeId] = { time: now, ...cur };
            }
          }

          set((s) => ({
            latestStats: stats,
            prevSnapshot: curSnap,
            prevNodeSnapshot: newNodeSnap,
            aggregateSeries: [...s.aggregateSeries, point].slice(-MAX_SERIES),
            nodeTimeSeries: newNodeSeries,
          }));
        } else {
          // No change — just update latestStats, don't emit a data point
          set({ latestStats: stats });
        }
      } else {
        // First poll — store baseline
        const curNodeSnap: Record<string, { time: number; bandwidth: number; messages: number; blocks: number }> = {};
        for (const [id, cum] of Object.entries(curNodeCum)) {
          curNodeSnap[id] = { time: now, ...cum };
        }
        set({
          latestStats: stats,
          prevSnapshot: curSnap,
          prevNodeSnapshot: curNodeSnap,
        });
      }
    } catch (e) {
      console.error("Failed to poll stats:", e);
    }
  },

  // --- Events ---
  events: [],
  lastEventTime: 0,
  eventsPaused: false,

  toggleEventsPause: () => set((s) => ({ eventsPaused: !s.eventsPaused })),

  handleEventBatch: (newEvents: OutputEvent[]) => {
    if (newEvents.length === 0) return;

    const maxTime = newEvents.reduce(
      (max, e) => Math.max(max, e.time_s),
      get().lastEventTime,
    );

    // Compute flashes from new events.
    // "produced" takes priority — don't let RBReceived overwrite it.
    const flashes: Record<string, "produced" | "received"> = {};
    for (const e of newEvents) {
      const node = e.message?.node;
      const type = e.message?.type;
      if (!node) continue;
      if (type === "RBGenerated") flashes[node] = "produced";
      else if (type === "RBReceived" && flashes[node] !== "produced") flashes[node] = "received";
    }

    set((s) => ({
      events: [...s.events, ...newEvents].slice(-MAX_EVENTS),
      lastEventTime: maxTime,
      nodeFlash: { ...s.nodeFlash, ...flashes },
    }));

    // Clear flashes after 600ms
    if (Object.keys(flashes).length > 0) {
      setTimeout(() => {
        set((s) => {
          const cleared = { ...s.nodeFlash };
          for (const id of Object.keys(flashes)) {
            if (cleared[id] === flashes[id]) cleared[id] = null;
          }
          return { nodeFlash: cleared };
        });
      }, 600);
    }
  },

  pollEvents: async () => {
    try {
      if (get().eventsPaused) return;
      const { lastEventTime } = get();
      const newEvents = await fetchEvents(lastEventTime);
      get().handleEventBatch(newEvents);
    } catch (e) {
      console.error("Failed to poll events:", e);
    }
  },

  // --- Flash ---
  nodeFlash: {},

  // --- Selection ---
  selectedNodeId: null,
  selectedEdge: null,

  selectNode: (id) => set({ selectedNodeId: id, selectedEdge: null }),
  selectEdge: (edge) => set({ selectedEdge: edge, selectedNodeId: null }),
}));
