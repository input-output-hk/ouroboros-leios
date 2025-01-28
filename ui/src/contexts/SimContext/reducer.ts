import { defaultState } from "./context";
import { ISimContextState, TSimContextActions } from "./types";

export const reducer = (
  state: ISimContextState,
  action: TSimContextActions,
): ISimContextState => {
  switch (action.type) {
    case "SET_ACTIVE_TAB": {
      return {
        ...state,
        activeTab: action.payload,
        blocks: {
          currentBlock: undefined
        }
      }
    }

    case "SET_CURRENT_NODE": {
      return {
        ...state, graph: {
          ...state.graph,
          currentNode: action.payload
        },
      }
    }

    case "SET_CURRENT_BLOCK": {
      return {
        ...state, blocks: {
          ...state.blocks,
          currentBlock: action.payload
        }
      }
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
              : action.payload.canvasScale ?? state.graph.canvasScale,
          canvasOffsetX:
            typeof action.payload.canvasOffsetX === "function"
              ? action.payload.canvasOffsetX(state.graph.canvasOffsetX)
              : action.payload.canvasOffsetX ?? state.graph.canvasOffsetX,
          canvasOffsetY:
            typeof action.payload.canvasOffsetY === "function"
              ? action.payload.canvasOffsetY(state.graph.canvasOffsetY)
              : action.payload.canvasOffsetY ?? state.graph.canvasOffsetY,
        }
      };
    }

    case "SET_BATCH_SIZE": {
      return {
        ...state,
        batchSize: action.payload
      }
    }

    case "BATCH_UPDATE": {
      return {
        ...state,
        ...action.payload,
      };
    }

    case "RESET_STATE":
      return defaultState;

    default:
      return state;
  }
};
