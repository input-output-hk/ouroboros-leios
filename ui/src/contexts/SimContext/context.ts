"use client";
import { DEFAULT_SCALE } from "@/app/constants";
import { Context, createContext, useContext } from "react";
import { ISimContext, ISimContextState, ISimulationAggregatedDataState } from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  progress: 0,
  nodes: new Map(),
  global: {
    praosTxOnChain: 0,
    leiosTxOnChain: 0,
  },
  lastNodesUpdated: []
};

export const defaultState: ISimContextState = {
  graph: {
    canvasRef: { current: null },
    canvasOffsetX: 0,
    canvasOffsetY: 0,
    canvasScale: DEFAULT_SCALE,
  },
  batchSize: 5000,
  aggregatedData: defaultAggregatedData,
  maxTime: 0,
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
}

export const SimContext: Context<ISimContext> = createContext({
  state: defaultState,
  dispatch: (_val) => { }
});
export const useSimContext = () => useContext(SimContext);
