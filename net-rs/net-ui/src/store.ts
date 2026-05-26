import { create } from "zustand";
import type {
  Topology,
  StatsSnapshot,
  OutputEvent,
  AggregatePoint,
  NodeSeriesPoint,
  ChainTreeEntry,
  ClusterControlConfig, AggregateNodeVotes,
} from "./types";
import {
  fetchTopology,
  fetchAllStats,
  fetchEvents,
  fetchConfig,
  restartCluster as apiRestartCluster,
  updateNodeConfig as apiUpdateNodeConfig,
  fetchAggregateNodeVotes
} from "./api";

const MAX_SERIES = 300; // ~5 min at 1s stats interval
const MAX_EVENTS = 500;

// Mutable event ring buffer — kept outside Zustand to avoid
// retaining old immutable array copies in React state snapshots.
const eventRing: OutputEvent[] = [];
export function getEvents(): readonly OutputEvent[] {
  return eventRing;
}

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
  prevSnapshot: { time: number; bandwidth: number; messages: number; blocks: number; forks: number } | null;
  prevNodeSnapshot: Record<string, { time: number; bandwidth: number; messages: number; blocks: number }>;
  aggregateSeries: AggregatePoint[];
  nodeTimeSeries: Record<string, NodeSeriesPoint[]>;
  networkChainTree: ChainTreeEntry[];
  networkTipCounts: Record<string, string[]>;
  pollStats: () => Promise<void>;

  // Events (actual events in eventRing, outside store)
  eventVersion: number;
  lastEventTime: number;
  eventsPaused: boolean;
  handleEventBatch: (events: OutputEvent[]) => void;
  pollEvents: () => Promise<void>;
  toggleEventsPause: () => void;

  // Node flash (block produced/received/rolled back)
  nodeFlash: Record<string, "rb-produced" | "rb-certified" | "rb-received" | "eb-produced" | "eb-received" | "vote-produced" | "vote-received" | "rolledback" | null>;

  // Edge flash queue (peer connect/disconnect).  Keyed by normalized
  // edge id `${min(from,to)}-${max(from,to)}`.  Stored as a queue so a
  // disconnect-then-reconnect (common during churn) shows red → green
  // in sequence rather than the latter overwriting the former.  The
  // display reads `edgeFlash[key][0]`; a per-edge timer shifts the
  // queue forward.
  edgeFlash: Record<string, ("connected" | "disconnected")[]>;
  // Steady-state edge status.  `connected` = at least one event for
  // this edge ended in PeerConnected; `disconnected` = the most
  // recent event was PeerDisconnected.  Edges with no events stay
  // undefined (gray default).  Drives the steady-state colour: pink
  // for disconnected, gray for connected/unknown.  Independent of
  // the flash queue.
  edgeStatus: Record<string, "connected" | "disconnected">;
  // (node_id, peer_id) → address learnt on PeerConnected; consulted
  // on PeerDisconnected (which carries no address) so we can map
  // back to the topology edge.
  peerAddrMap: Record<string, string>;

  // Selection
  selectedNodeId: string | null;
  selectedEdge: { from: number; to: number } | null;
  selectNode: (id: string | null) => void;
  selectEdge: (edge: { from: number; to: number } | null) => void;

  // Cluster control
  clusterConfig: ClusterControlConfig | null;
  restarting: boolean;
  loadConfig: () => Promise<void>;
  restartCluster: (config: ClusterControlConfig) => Promise<void>;

  // Voting panel data (column-major: [slot][row])
  votingMatrix: ("NoEvent" | "RBReceived" | "EBReceived" | "VoteCast")[][];
  votingSlotStart: number;
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
  networkChainTree: [],
  networkTipCounts: {},

  // Voting panel
  votingMatrix: [],
  votingSlotStart: 0,

  pollStats: async () => {
    try {
      const stats = await fetchAllStats();
      const now = Date.now();
      const { prevSnapshot, prevNodeSnapshot } = get();

      // Compute current cumulative totals
      let totalBandwidth = 0;
      let totalMessages = 0;
      let totalBlocks = 0;
      let curSlot = 0;
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
        curSlot = snap.slot;
      }

      // Count distinct chain tips (forks)
      const tipSet = new Set<string>();
      for (const snap of Object.values(stats)) {
        if (snap.tip_hash) tipSet.add(snap.tip_hash);
      }
      const curForks = tipSet.size;

      // Aggregate network-wide chain tree, accumulating across polls so
      // gaps don't appear when nodes are at different chain heights.
      // Skip carry-forward while restarting so stale entries don't persist.
      const mergedEntries = new Map<string, ChainTreeEntry>();
      if (!get().restarting) {
        for (const e of get().networkChainTree) {
          mergedEntries.set(e.hash, e);
        }
      }
      const tipCounts: Record<string, string[]> = {};
      for (const snap of Object.values(stats)) {
        if (snap.chain_tree) {
          for (const e of snap.chain_tree) {
            mergedEntries.set(e.hash, e);
          }
        }
        if (snap.tip_hash) {
          (tipCounts[snap.tip_hash] ??= []).push(snap.node_id);
        }
      }
      // Prune blocks too far behind the tip.
      let maxBn = 0;
      for (const e of mergedEntries.values()) {
        if (e.block_number > maxBn) maxBn = e.block_number;
      }
      const pruneBelow = maxBn - 30;
      for (const [hash, e] of mergedEntries) {
        if (e.block_number < pruneBelow) mergedEntries.delete(hash);
      }
      const networkChainTree = [...mergedEntries.values()].sort(
        (a, b) => a.block_number - b.block_number,
      );

      const curSnap = { time: now, bandwidth: totalBandwidth, messages: totalMessages, blocks: totalBlocks, forks: curForks };

      const VOTING_SLOTS = 24;
      const topoNodes = get().topology?.nodes ?? [];
      const nodeCount = topoNodes.length;
      const slotStart = Math.max(0, curSlot - VOTING_SLOTS + 1);

      let aggregated_votes: Array<AggregateNodeVotes> = [];

      for (let slot: number = curSlot - VOTING_SLOTS; slot <= curSlot; slot++) {
        aggregated_votes.push(await fetchAggregateNodeVotes(slot));
      }

      const nextMatrix: ("NoEvent" | "RBReceived" | "EBReceived" | "VoteCast" | "Committee")[][] = Array.from(
        {length: VOTING_SLOTS},
        (_, i) => {
          const votes = aggregated_votes[i]?.node_statuses;
          if (votes) {
            return topoNodes.map((n) => {
              const v = votes[n.node_id];
              console.log(n.node_id);
              console.log(votes[n.node_id]);
              if (!v) return "NoEvent" as const;
              if (v.vote_cast) return "VoteCast" as const;
              if (v.eb_received) return "EBReceived" as const;
              if (v.rb_received) return "RBReceived" as const;
              if (v.perm_committee_member) return "Committee" as const;
              return "NoEvent" as const;
            });
          }
          return Array.from({length: nodeCount}, () => "NoEvent" as const);
        }
      )

      const votingSlotStart = slotStart;

      if (prevSnapshot) {
        const changed =
          curSnap.bandwidth !== prevSnapshot.bandwidth ||
          curSnap.messages !== prevSnapshot.messages ||
          curSnap.blocks !== prevSnapshot.blocks ||
          curSnap.forks !== prevSnapshot.forks;

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
            forks: curForks,
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
            networkChainTree,
            networkTipCounts: tipCounts,
            votingMatrix: nextMatrix,
            votingSlotStart,
          }));
        } else {
          // No change — just update latestStats, don't emit a data point
          set({
            latestStats: stats, networkChainTree, networkTipCounts: tipCounts,
            votingMatrix: nextMatrix,
            votingSlotStart,
          });
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
          networkChainTree,
          networkTipCounts: tipCounts,
          votingMatrix: nextMatrix,
          votingSlotStart,
        });
      }
    } catch (e) {
      console.error("Failed to poll stats:", e);
    }
  },

  // --- Events ---
  eventVersion: 0,
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
    // Priority order: rolledback > rb-certified > produced > received.
    // RbCertifiedEb fires alongside RBGenerated on the same producer, and
    // is the more specific signal — it should override rb-produced.
    type FlashType = "rb-produced" | "rb-certified" | "rb-received" | "eb-produced" | "eb-received" | "vote-produced" | "vote-received" | "rolledback";
    const produced = new Set(["rb-produced", "rb-certified", "eb-produced", "vote-produced"]);
    const flashes: Record<string, FlashType> = {};

    // Edge flashes: PeerConnected → green, PeerDisconnected → red.
    // Resolved via the topology's listen_address index; events with
    // ephemeral source ports (inbound connections) won't match and
    // simply don't flash — which is fine, the outbound-side event
    // for the same connection will.  A queue per edge so rapid
    // disconnect→reconnect plays as red→green in sequence.
    type EdgeFlashType = "connected" | "disconnected";
    const edgeFlashes: Record<string, EdgeFlashType[]> = {};
    const statusUpdates: Record<string, EdgeFlashType> = {};
    const peerAddrUpdates: Record<string, string> = {};
    const topology = get().topology;
    const addrToNodeIdx: Map<string, number> | null = topology
      ? new Map(
          topology.nodes.map((n) => [
            `${n.listen_address}`,
            n.index,
          ]),
        )
      : null;
    const nodeIdToIdx: Map<string, number> | null = topology
      ? new Map(topology.nodes.map((n) => [n.node_id, n.index]))
      : null;
    const peerAddrMap = get().peerAddrMap;
    const resolvePeerAddr = (node: string, peer_id: string): string | undefined => {
      return (
        peerAddrUpdates[`${node}|${peer_id}`] ?? peerAddrMap[`${node}|${peer_id}`]
      );
    };
    const edgeKey = (a: number, b: number) => {
      const lo = Math.min(a, b);
      const hi = Math.max(a, b);
      return `${lo}-${hi}`;
    };

    for (const e of newEvents) {
      const node = e.message?.node as string | undefined;
      const type = e.message?.type as string | undefined;
      if (!node) continue;

      // -- Node flash --
      if (type === "RolledBack") {
        flashes[node] = "rolledback";
      } else {
        const cur = flashes[node];
        if (cur !== "rolledback") {
          if (type === "RbCertifiedEb") flashes[node] = "rb-certified";
          else if (type === "RBGenerated" && cur !== "rb-certified") flashes[node] = "rb-produced";
          else if (type === "EBGenerated") flashes[node] = "eb-produced";
          else if (type === "VTBundleGenerated") flashes[node] = "vote-produced";
          else if (type === "RBReceived" && (!cur || !produced.has(cur))) flashes[node] = "rb-received";
          else if (type === "EBReceived" && (!cur || !produced.has(cur))) flashes[node] = "eb-received";
          else if (type === "VTBundleReceived" && (!cur || !produced.has(cur))) flashes[node] = "vote-received";
        }
      }

      // -- Edge flash + steady-state status --
      // Each event flashes in temporal order.  In this cluster the
      // typical churn cycle is connect → die rather than die →
      // reconnect, so the user sees green → red on each flicker.
      // After the flash clears, edgeStatus determines the steady
      // colour: pink if the most recent event was a disconnect,
      // gray if the most recent was a connect (or no events yet).
      if (type === "PeerConnected" || type === "PeerDisconnected") {
        const peer_id = e.message?.peer_id as string | undefined;
        if (!peer_id || !addrToNodeIdx || !nodeIdToIdx) continue;
        let addr: string | undefined;
        if (type === "PeerConnected") {
          addr = e.message?.address as string | undefined;
          if (addr) peerAddrUpdates[`${node}|${peer_id}`] = addr;
        } else {
          addr = resolvePeerAddr(node, peer_id);
        }
        if (!addr) continue;
        const peerIdx = addrToNodeIdx.get(addr);
        const localIdx = nodeIdToIdx.get(node);
        if (peerIdx === undefined || localIdx === undefined) continue;
        const key = edgeKey(localIdx, peerIdx);
        const state: EdgeFlashType =
          type === "PeerConnected" ? "connected" : "disconnected";
        const seq = (edgeFlashes[key] ??= []);
        // Dedup consecutive duplicates so a re-announce of the same
        // state doesn't elongate the animation pointlessly.
        if (seq[seq.length - 1] !== state) {
          seq.push(state);
        }
        // edgeStatus is the most recent state per edge.  Repeatedly
        // overwritten as events arrive; settled value drives the
        // steady-state colour after the flash queue drains.
        statusUpdates[key] = state;
      }
    }

    // Mutate ring buffer in place — no immutable copy in store state.
    for (const e of newEvents) {
      if (eventRing.length >= MAX_EVENTS) eventRing.shift();
      eventRing.push(e);
    }

    // Merge edge-flash queues with whatever's already pending for each
    // edge.  An edge that's actively animating gets its incoming
    // events appended to the existing queue (with consecutive-duplicate
    // dedup); an edge that's idle starts fresh and gets a timer.
    const newlyAnimating: string[] = [];
    set((s) => {
      const mergedEdge: typeof s.edgeFlash = { ...s.edgeFlash };
      for (const [key, incoming] of Object.entries(edgeFlashes)) {
        const existing = mergedEdge[key];
        if (existing && existing.length > 0) {
          // Concat; suppress same-state duplicates at the seam.
          let i = 0;
          if (existing[existing.length - 1] === incoming[0]) i = 1;
          mergedEdge[key] = [...existing, ...incoming.slice(i)];
        } else {
          mergedEdge[key] = incoming;
          newlyAnimating.push(key);
        }
      }

      return {
        eventVersion: s.eventVersion + 1,
        lastEventTime: maxTime,
        nodeFlash: { ...s.nodeFlash, ...flashes },
        edgeFlash: mergedEdge,
        edgeStatus:
          Object.keys(statusUpdates).length > 0
            ? { ...s.edgeStatus, ...statusUpdates }
            : s.edgeStatus,
        peerAddrMap:
          Object.keys(peerAddrUpdates).length > 0
            ? { ...s.peerAddrMap, ...peerAddrUpdates }
            : s.peerAddrMap,
      };
    });

    // Clear node flashes after 600ms
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
    // Per-edge animator: shift the queue every 450ms until empty.
    // Only kick off animators for edges that just transitioned from
    // idle → animating; edges already in flight have their own timer
    // running.  Each step displays the head of the queue for 450ms.
    const advance = (key: string) => {
      setTimeout(() => {
        let shouldContinue = false;
        set((s) => {
          const cur = s.edgeFlash[key] ?? [];
          if (cur.length === 0) return s;
          const next = cur.slice(1);
          shouldContinue = next.length > 0;
          return { edgeFlash: { ...s.edgeFlash, [key]: next } };
        });
        if (shouldContinue) advance(key);
      }, 450);
    };
    for (const key of newlyAnimating) advance(key);
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
  edgeFlash: {},
  edgeStatus: {},
  peerAddrMap: {},

  // --- Selection ---
  selectedNodeId: null,
  selectedEdge: null,

  selectNode: (id) => set({ selectedNodeId: id, selectedEdge: null }),
  selectEdge: (edge) => set({ selectedEdge: edge, selectedNodeId: null }),

  // --- Cluster control ---
  clusterConfig: null,
  restarting: false,
  updating: false,

  loadConfig: async () => {
    try {
      const config = await fetchConfig();
      set({ clusterConfig: config });
    } catch (e) {
      console.error("Failed to load config:", e);
    }
  },

  restartCluster: async (config) => {
    set({ restarting: true });
    try {
      const ok = await apiRestartCluster(config);
      if (ok) {
        // Clear local state from the old cluster.
        eventRing.length = 0;
        set({
          latestStats: {},
          prevSnapshot: null,
          prevNodeSnapshot: {},
          aggregateSeries: [],
          nodeTimeSeries: {},
          networkChainTree: [],
          networkTipCounts: {},
          eventVersion: 0,
          lastEventTime: 0,
          nodeFlash: {},
          edgeFlash: {},
          edgeStatus: {},
          peerAddrMap: {},
          topology: null,
          layoutReady: false,
          nodePositions: {},
          selectedNodeId: null,
          selectedEdge: null,
          votingMatrix: [],
          votingSlotStart: 0,
        });
        // Wait for new nodes to start, then reload topology + config.
        await new Promise((resolve) => setTimeout(resolve, 2000));
        await get().loadTopology();
        await get().loadConfig();
      }
    } finally {
      set({ restarting: false });
    }
  },

  updateNodeConfig: async (nodeConfig: Record<string, unknown>) => {
    set({ updating: true });
    try {
      await apiUpdateNodeConfig(nodeConfig);
      await get().loadConfig();
    } finally {
      set({ updating: false });
    }
  },
}));
