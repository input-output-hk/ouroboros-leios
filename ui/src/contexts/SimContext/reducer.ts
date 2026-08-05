import { defaultAggregatedData } from "./context";
import {
  ISimContextState,
  TSimContextActions,
  EConnectionState,
} from "./types";
import {
  buildChainAtTime,
  computeAggregatedDataAtTime,
  clearLatencyCache,
} from "@/utils/timelineAggregation";

export const reducer = (
  state: ISimContextState,
  action: TSimContextActions,
): ISimContextState => {
  switch (action.type) {
    case "SET_SCENARIOS": {
      const allScenarios = action.payload;
      const scenario = allScenarios[0];
      return {
        ...state,
        allScenarios,
        activeScenario: scenario.name,
        maxTime: scenario.duration,
        tracePath: scenario.trace || "",
        topologyPath: scenario.topology,
      };
    }

    case "SET_SCENARIO": {
      const scenario = state.allScenarios.find(
        (s) => s.name === action.payload,
      );
      if (!scenario) {
        return state;
      }
      return {
        ...state,
        aggregatedData: defaultAggregatedData,
        selectedBlock: undefined,
        activeScenario: scenario.name,
        autoStart: action.autoStart || false,
        tracePath: scenario.trace || "",
        lokiHost: scenario.loki,
        lokiConnectionState: EConnectionState.NotConnected,
        topologyPath: scenario.topology,
        topologyLoaded:
          state.topologyLoaded && scenario.topology === state.topologyPath,
        graph: {
          ...state.graph,
          currentNode: undefined,
          currentEdge: undefined,
        },
        // Reset timeline when switching scenarios
        events: [],
        currentTime: 0,
        minTime: 0,
        maxTime: scenario.duration,
      };
    }

    case "SET_CURRENT_NODE": {
      return {
        ...state,
        graph: {
          ...state.graph,
          currentNode: action.payload,
          currentEdge: undefined, // Clear edge selection when selecting a node
        },
      };
    }

    case "SET_CURRENT_EDGE": {
      return {
        ...state,
        graph: {
          ...state.graph,
          currentEdge: action.payload,
          currentNode: undefined, // Clear node selection when selecting an edge
        },
      };
    }

    case "SET_CANVAS_PROPS": {
      return {
        ...state,
        graph: {
          ...state.graph,
          canvasScale:
            typeof action.payload.canvasScale === "function"
              ? action.payload.canvasScale(state.graph.canvasScale)
              : (action.payload.canvasScale ?? state.graph.canvasScale),
          canvasOffsetX:
            typeof action.payload.canvasOffsetX === "function"
              ? action.payload.canvasOffsetX(state.graph.canvasOffsetX)
              : (action.payload.canvasOffsetX ?? state.graph.canvasOffsetX),
          canvasOffsetY:
            typeof action.payload.canvasOffsetY === "function"
              ? action.payload.canvasOffsetY(state.graph.canvasOffsetY)
              : (action.payload.canvasOffsetY ?? state.graph.canvasOffsetY),
        },
      };
    }

    case "BATCH_UPDATE": {
      return {
        ...state,
        ...action.payload,
      };
    }

    case "RESET_TOPOLOGY":
      clearLatencyCache();
      return {
        ...state,
        topography: { links: new Map(), nodes: new Map() },
        topologyPath: action.payload,
        topologyLoaded: false,
      };

    case "SET_TOPOLOGY":
      if (action.payload.topologyPath != state.topologyPath) {
        return state;
      }
      clearLatencyCache();
      return {
        ...state,
        topography: action.payload.topology,
        topologyLoaded: true,
      };

    case "ADD_TIMELINE_EVENT_BATCH": {
      // Keep `events` ordered by `time_s`. The aggregator relies on this: it
      // stops scanning at the first event past the current time, so an
      // out-of-order event would truncate the scan and silently drop later
      // events from every count. The live Loki path interleaves
      // independently-delivered per-direction streams, so batches arrive out
      // of order. Merge-insert the (small) sorted batch into the already-sorted
      // list in O(n + m); a full re-sort each batch would be O(n log n),
      // untenable once a demo reaches hundreds of thousands of events.
      const incoming = [...action.payload].sort((a, b) => a.time_s - b.time_s);
      const prev = state.events;
      const merged: typeof prev = new Array(prev.length + incoming.length);
      let pi = 0;
      let ii = 0;
      let mi = 0;
      while (pi < prev.length && ii < incoming.length) {
        if (prev[pi].time_s <= incoming[ii].time_s) {
          merged[mi++] = prev[pi++];
        } else {
          merged[mi++] = incoming[ii++];
        }
      }
      while (pi < prev.length) merged[mi++] = prev[pi++];
      while (ii < incoming.length) merged[mi++] = incoming[ii++];
      const newEvents = merged;

      if (newEvents.length === 0) {
        return {
          ...state,
          events: newEvents,
        };
      }

      // `newEvents` is sorted, so the bounds are its endpoints — O(1), and
      // avoids `Math.min(...timestamps)` overflowing the call stack at large
      // event counts.
      const minEventTime = newEvents[0].time_s;
      const maxEventTime = newEvents[newEvents.length - 1].time_s;

      // Update timeline bounds and clamp current time
      const newMinTime =
        state.minTime == 0
          ? minEventTime
          : Math.min(state.minTime, minEventTime);
      const newMaxTime = Math.max(state.maxTime, maxEventTime);

      const clampedCurrentTime = Math.max(
        newMinTime,
        Math.min(state.currentTime, newMaxTime),
      );

      return {
        ...state,
        events: newEvents,
        minTime: newMinTime,
        maxTime: newMaxTime,
        currentTime: clampedCurrentTime,
        aggregatedData: {
          ...state.aggregatedData,
          chain: buildChainAtTime(newEvents, clampedCurrentTime),
        },
      };
    }

    case "SET_TIMELINE_TIME": {
      const newTime = Math.max(
        state.minTime,
        Math.min(action.payload, state.maxTime),
      );

      // Recompute complete aggregated data based on new timeline position
      const nodeIds = Array.from(state.topography.nodes.keys());

      const newAggregatedData = computeAggregatedDataAtTime(
        state.events,
        newTime,
        nodeIds,
        state.topography,
      );

      if (state.graph.currentNode) {
        const newState = newAggregatedData.nodes.get(state.graph.currentNode);
        // TODO: only log when different
        console.log(`Node ${state.graph.currentNode} state`, newState);
      }

      return {
        ...state,
        currentTime: newTime,
        aggregatedData: newAggregatedData,
      };
    }

    case "SET_TIMELINE_PLAYING":
      return {
        ...state,
        isPlaying: action.payload,
      };

    case "SET_TIMELINE_SPEED":
      return {
        ...state,
        speedMultiplier: action.payload,
      };

    case "RESET_TIMELINE":
      return {
        ...state,
        events: [],
        currentTime: 0,
        minTime: 0,
        maxTime: 0,
        isPlaying: false,
        speedMultiplier: 1,
        aggregatedData: defaultAggregatedData,
        selectedBlock: undefined,
        lokiDroppedEntries: 0,
      };

    case "SET_LOKI_CONNECTION_STATE":
      return {
        ...state,
        lokiConnectionState: action.payload,
      };

    case "ADD_LOKI_DROPPED_ENTRIES":
      return {
        ...state,
        lokiDroppedEntries: state.lokiDroppedEntries + action.payload,
      };

    case "SET_LAYOUT_MODE":
      return {
        ...state,
        layoutMode: action.payload,
      };

    case "SET_NODE_POSITIONS": {
      const newNodes = new Map(state.topography.nodes);
      for (const [id, pos] of action.payload) {
        const existing = newNodes.get(id);
        if (existing) {
          newNodes.set(id, { ...existing, fx: pos.fx, fy: pos.fy });
        }
      }
      return {
        ...state,
        topography: { ...state.topography, nodes: newNodes },
      };
    }

    case "SET_MERCATOR_PARAMS":
      return {
        ...state,
        mercatorParams: action.payload,
      };

    case "SET_MAP_GEOJSON":
      return {
        ...state,
        mapGeoJson: action.payload,
      };

    case "SET_SELECTED_BLOCK":
      return {
        ...state,
        selectedBlock: action.payload,
      };

    default:
      return state;
  }
};
