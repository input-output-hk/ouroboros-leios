import { createContext, useContext } from "react";
import { ESpeedOptions, IGraphContextState } from "./types";

export const defaultState: IGraphContextState = {
  canvasRef: { current: null },
  currentTime: 0,
  generatedMessages: new Set(),
  intervalId: { current: null },
  maxTime: 0,
  messages: [],
  playing: false,
  simulationPauseTime: { current: 0 },
  simulationStartTime: { current: 0 },
  sentTxs: new Set(),
  speed: ESpeedOptions["3/10"],
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
  transactions: new Map(),
  setCurrentTime: () => {},
  setGeneratedMessages: () => {},
  setMaxTime: () => {},
  setMessages: () => {},
  setPlaying: () => {},
  setSentTxs: () => {},
  setSpeed: () => {},
  setTopography: () => {},
  setTopographyLoaded: () => {},
  setTransactions: () => {}
}

export const GraphContext = createContext(defaultState);
export const useGraphContext = () => useContext(GraphContext);
