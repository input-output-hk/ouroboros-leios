"use client";
import { Context, createContext, useContext } from "react";
import { ESpeedOptions, IGraphContext, IGraphContextState, ISimulationAggregatedDataState } from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  nodes: new Map()
};

export const defaultState: IGraphContextState = {
  canvasRef: { current: null },
  aggregatedData: { current: defaultAggregatedData },
  currentTime: 0,
  generatedMessages: [],
  intervalId: { current: undefined },
  maxTime: 0,
  messages: new Map(),
  playing: false,
  simulationPauseTime: { current: 0 },
  simulationStartTime: { current: 0 },
  sentTxs: [],
  speed: ESpeedOptions["3% Speed"],
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
}

export const GraphContext: Context<IGraphContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {}
});
export const useGraphContext = () => useContext(GraphContext);
