"use client";
import { Context, createContext, useContext } from "react";
import { ESpeedOptions, IGraphContext, IGraphContextState } from "./types";

export const defaultState: IGraphContextState = {
  canvasRef: { current: null },
  transactionsByIdRef: { current: new Map() },
  txGeneratedMessagesById: { current: new Map() },
  txReceivedMessagesById: { current: new Map() },
  txSentMessagesById: { current: new Map() },
  currentTime: 0,
  generatedMessages: [],
  intervalId: { current: null },
  maxTime: 0,
  messages: new Map(),
  playing: false,
  simulationPauseTime: { current: 0 },
  simulationStartTime: { current: 0 },
  sentTxs: [],
  speed: ESpeedOptions["3% Speed"],
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
  transactions: new Map(),
}

export const GraphContext: Context<IGraphContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {}
});
export const useGraphContext = () => useContext(GraphContext);
