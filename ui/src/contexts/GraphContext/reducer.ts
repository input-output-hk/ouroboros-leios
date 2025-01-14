import { defaultState } from "./context";
import { IGraphContextState, TGraphContextActions } from "./types";

export const reducer = (
  state: IGraphContextState,
  action: TGraphContextActions,
): IGraphContextState => {
  switch (action.type) {
    case "SET_CURRENT_NODE": {
      return { ...state, currentNode: action.payload };
    }

    case "SET_AGGREGATED_DATA": {
      return { ...state, aggregatedData: action.payload };
    }

    case "SET_CANVAS_PROPS": {
      return {
        ...state,
        canvasScale:
          typeof action.payload.canvasScale === "function"
            ? action.payload.canvasScale(state.canvasScale)
            : action.payload.canvasScale || state.canvasScale,
        canvasOffsetX:
          typeof action.payload.canvasOffsetX === "function"
            ? action.payload.canvasOffsetX(state.canvasOffsetX)
            : action.payload.canvasOffsetX || state.canvasOffsetX,
        canvasOffsetY:
          typeof action.payload.canvasOffsetY === "function"
            ? action.payload.canvasOffsetY(state.canvasOffsetY)
            : action.payload.canvasOffsetY || state.canvasOffsetY,
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
