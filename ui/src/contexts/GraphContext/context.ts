import { createContext, useContext } from "react";
import { ESpeedOptions, IGraphContextState } from "./types";

export const defaultState: IGraphContextState = {
  currentTime: 0,
  intervalId: { current: null },
  maxTime: 0,
  messages: [],
  playing: false,
  simulationPauseTime: { current: 0 },
  simulationStartTime: { current: 0 },
  sentTxs: new Set(),
  speed: ESpeedOptions["3/10"],
  topography: { links: [], nodes: [] },
  transactions: new Map(),
  setCurrentTime: () => {},
  setMaxTime: () => {},
  setMessages: () => {},
  setPlaying: () => {},
  setSentTxs: () => {},
  setSpeed: () => {},
  setTopography: () => {},
  setTransactions: () => {}
}

export const GraphContext = createContext(defaultState);
export const useGraphContext = () => useContext(GraphContext);
