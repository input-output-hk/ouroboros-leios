import { defaultAggregatedData } from "./context";
import { ISimContextState, TSimContextActions } from "./types";
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
        maxTime: scenario.duration,
        tracePath: scenario.trace || "",
        lokiHost: scenario.loki,
        lokiConnected: false,
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

    case "ADD_TIMELINE_EVENT_BATCH":
      return {
        ...state,
        events: [...state.events, ...action.payload],
      };

    case "SET_TIMELINE_TIME": {
      const newTime = action.payload;

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
        isPlaying: false,
        speedMultiplier: 1,
      };

    case "SET_LOKI_CONNECTED":
      return {
        ...state,
        lokiConnected: action.payload,
      };

    default:
      return state;
  }
};
