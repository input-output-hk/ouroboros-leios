import { defaultAggregatedData } from "./context";
import { ISimContextState, TSimContextActions } from "./types";
import { computeAggregatedDataAtTime } from "@/utils/timelineAggregation";

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
        tracePath: scenario.trace,
        aggregated: scenario.aggregated,
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
        tracePath: scenario.trace,
        aggregated: scenario.aggregated,
        topologyPath: scenario.topology,
        topologyLoaded:
          state.topologyLoaded && scenario.topology === state.topologyPath,
        graph: {
          ...state.graph,
          currentNode: undefined,
        },
        blocks: {
          currentBlock: undefined,
        },
        // Reset timeline when switching scenarios
        events: [],
        currentTime: 0,
      };
    }

    case "SET_ACTIVE_TAB": {
      return {
        ...state,
        activeTab: action.payload,
        graph: {
          ...state.graph,
          currentNode:
            state.activeTab === action.payload
              ? state.graph.currentNode
              : undefined,
        },
        blocks: {
          currentBlock: undefined,
        },
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

    case "SET_CURRENT_BLOCK": {
      return {
        ...state,
        blocks: {
          ...state.blocks,
          currentBlock: action.payload,
        },
      };
    }

    case "SET_AGGREGATED_DATA": {
      return { ...state, aggregatedData: action.payload };
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

    case "SET_SPEED": {
      return {
        ...state,
        speedMultiplier: action.payload.speedMultiplier,
      };
    }

    case "BATCH_UPDATE": {
      return {
        ...state,
        ...action.payload,
      };
    }

    case "RESET_TOPOLOGY":
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
      return {
        ...state,
        topography: action.payload.topology,
        topologyLoaded: true,
      };

    case "ADD_TIMELINE_EVENT":
      return {
        ...state,
        events: [...state.events, action.payload],
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

    case "STEP_TIMELINE_FORWARD": {
      const maxTime = state.events.length > 0 
        ? state.events[state.events.length - 1].time_s 
        : state.maxTime;
      const newTime = Math.min(state.currentTime + action.payload, maxTime);
      
      // Recompute aggregated data for the new time
      const nodeIds = Array.from(state.topography.nodes.keys());
      const newAggregatedData = computeAggregatedDataAtTime(
        state.events,
        newTime,
        nodeIds,
      );
      
      return {
        ...state,
        currentTime: newTime,
        aggregatedData: newAggregatedData,
      };
    }

    case "STEP_TIMELINE_BACKWARD": {
      const newTime = Math.max(state.currentTime - action.payload, 0);
      
      // Recompute aggregated data for the new time
      const nodeIds = Array.from(state.topography.nodes.keys());
      const newAggregatedData = computeAggregatedDataAtTime(
        state.events,
        newTime,
        nodeIds,
      );
      
      return {
        ...state,
        currentTime: newTime,
        aggregatedData: newAggregatedData,
      };
    }

    case "RESET_TIMELINE":
      return {
        ...state,
        events: [],
        currentTime: 0,
        isPlaying: false,
        speedMultiplier: 1,
      };

    default:
      return state;
  }
};
