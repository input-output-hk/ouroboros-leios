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

    case "REMOVE_GENERATED_MESSAGE": {
      const newSet = new Set(state.generatedMessages);
      newSet.delete(action.payload);
      return { ...state, generatedMessages: newSet };
    }

    case "SET_MAX_TIME":
      return { ...state, maxTime: action.payload };

    case "ADD_MESSAGE": {
      const newMessages = new Map(state.messages);
      newMessages.set(action.payload.time, action.payload);
      return { ...state, messages: newMessages };
    }

    case "ADD_MESSAGES": {
      const newPrev = new Map(state.messages);
      newPrev.forEach(v => {
        if (state.currentTime > v.time / 1_000_000) {
          newPrev.delete(v.time);
        }
      })

      const newMessages = new Map([...newPrev, ...action.payload]);
      return { ...state, messages: newMessages };
    }

    case "REMOVE_MESSAGE": {
      const newMessages = new Map(state.messages);
      newMessages.delete(action.payload);
      return { ...state, messages: newMessages };
    }

    case "REMOVE_MESSAGES": {
      debugger;
      const newMessages = new Map(state.messages);
      action.payload.forEach((time) => {
        newMessages.delete(time);
      });
      return { ...state, messages: newMessages };
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

    case "REMOVE_SENT_TX": {
      const newSet = new Set(state.sentTxs);
      newSet.delete(action.payload);
      return { ...state, sentTxs: newSet };
    }

    case "SET_SPEED":
      return { ...state, speed: action.payload };

    case "SET_TOPOGRAPHY":
      return { ...state, topography: action.payload };

    case "SET_TOPOGRAPHY_LOADED":
      return { ...state, topographyLoaded: action.payload };

    case "SET_TRANSACTIONS": {
      return { ...state, transactions: action.payload };
    }

    case "REMOVE_TRANSACTION": {
      debugger;
      const newTxs = new Map(state.transactions);
      newTxs.delete(action.payload);
      return { ...state, transactions: newTxs };
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
