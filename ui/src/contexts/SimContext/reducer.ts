import { defaultAggregatedData } from "./context";
import {
  ISimContextState,
  TSimContextActions,
  EConnectionState,
} from "./types";
import {
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
      const newEvents = [...state.events, ...action.payload];

      if (newEvents.length === 0) {
        return {
          ...state,
          events: newEvents,
        };
      }

      // Calculate timeline bounds
      const timestamps = newEvents.map((event) => event.time_s);
      const minEventTime = Math.min(...timestamps);
      const maxEventTime = Math.max(...timestamps);

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
      };

    case "SET_LOKI_CONNECTION_STATE":
      return {
        ...state,
        lokiConnectionState: action.payload,
      };

    default:
      return state;
  }
};
