import { defaultState } from "./context";
import { IGraphContextState, TGraphContextActions } from "./types";

export const reducer = (
  state: IGraphContextState,
  action: TGraphContextActions,
): IGraphContextState => {
  switch (action.type) {
    case "SET_CURRENT_TIME":
      return { ...state, currentTime: action.payload };

    case "ADD_GENERATED_MESSAGE": {
      const newSet = new Set(state.generatedMessages);
      newSet.add(action.payload);
      return { ...state, generatedMessages: newSet };
    }

    case "SET_GENERATED_MESSSAGES": {
      return { ...state, generatedMessages: action.payload };
    }

    case "REMOVE_GENERATED_MESSAGE": {
      const newSet = new Set(state.generatedMessages);
      newSet.delete(action.payload);
      return { ...state, generatedMessages: newSet };
    }

    case "SET_PLAYING": {
      return { ...state, playing: action.payload };
    }

    case "TOGGLE_PLAYING": {
      return { ...state, playing: !state.playing };
    }

    case "ADD_SENT_TX": {
      const newSet = new Set(state.sentTxs);
      newSet.add(action.payload);
      return { ...state, sentTxs: newSet };
    }

    case "SET_SENT_TXS": {
      return { ...state, sentTxs: action.payload };
    }

    case "REMOVE_SENT_TX": {
      const newSet = new Set(state.sentTxs);
      newSet.delete(action.payload);
      return { ...state, sentTxs: newSet };
    }

    case "SET_SPEED": {
      return { ...state, speed: action.payload };
    }

    case "BATCH_UPDATE": {
      return {
        ...state,
        ...action.payload
      }
    }

    case "RESET_STATE":
      return defaultState;

    default:
      return state;
  }
};
