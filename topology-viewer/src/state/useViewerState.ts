import { create } from "zustand";
import type { AggregateBy, NodeFeature, TopologyData } from "../data/types";

export interface ViewerState {
  topologyId: string;
  topology: TopologyData | null;
  loading: boolean;
  error: string | null;

  aggregateBy: AggregateBy;
  showNodes: boolean;
  showCorridors: boolean;
  showSpread: boolean;

  // Filter: providers excluded from rendering ("failure scenario" toggle)
  excludedProviders: Set<string>;

  hoverNode: NodeFeature | null;

  setTopologyId: (id: string) => void;
  setTopology: (data: TopologyData) => void;
  setLoading: (b: boolean) => void;
  setError: (e: string | null) => void;
  setAggregateBy: (a: AggregateBy) => void;
  setShowNodes: (b: boolean) => void;
  setShowCorridors: (b: boolean) => void;
  setShowSpread: (b: boolean) => void;
  toggleExcludedProvider: (p: string) => void;
  clearExcludedProviders: () => void;
  setHoverNode: (n: NodeFeature | null) => void;
}

export const useViewerState = create<ViewerState>((set) => ({
  topologyId: "topology-v4-mainnet",
  topology: null,
  loading: true,
  error: null,
  aggregateBy: "continent",
  showNodes: true,
  showCorridors: true,
  showSpread: false,
  excludedProviders: new Set(),
  hoverNode: null,

  setTopologyId: (id) => set({ topologyId: id, loading: true }),
  setTopology: (data) => set({ topology: data, loading: false, error: null }),
  setLoading: (b) => set({ loading: b }),
  setError: (e) => set({ error: e, loading: false }),
  setAggregateBy: (a) => set({ aggregateBy: a }),
  setShowNodes: (b) => set({ showNodes: b }),
  setShowCorridors: (b) => set({ showCorridors: b }),
  setShowSpread: (b) => set({ showSpread: b }),
  toggleExcludedProvider: (p) =>
    set((s) => {
      const next = new Set(s.excludedProviders);
      if (next.has(p)) next.delete(p);
      else next.add(p);
      return { excludedProviders: next };
    }),
  clearExcludedProviders: () => set({ excludedProviders: new Set() }),
  setHoverNode: (n) => set({ hoverNode: n }),
}));
