"use client";
import { Context, createContext, useContext } from "react";
import { ESpeedOptions, IGraphContext, IGraphContextState } from "./types";

export const defaultState: IGraphContextState = {
  canvasRef: { current: null },
  currentTime: 0,
  generatedMessages: new Set(),
  intervalId: { current: null },
  maxTime: 0,
  messages: new Map(),
  playing: false,
  simulationPauseTime: { current: 0 },
  simulationStartTime: { current: 0 },
  sentTxs: new Set(),
  speed: ESpeedOptions["1/300"],
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
  transactions: new Map(),
}

export const GraphContext: Context<IGraphContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {}
});
export const useGraphContext = () => useContext(GraphContext);
