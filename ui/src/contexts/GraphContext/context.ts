"use client";
import { DEFAULT_SCALE } from "@/app/constants";
import { Context, createContext, useContext } from "react";
import { IGraphContext, IGraphContextState, ISimulationAggregatedDataState } from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  progress: 0,
  nodes: new Map(),
  lastNodesUpdated: []
};

export const defaultState: IGraphContextState = {
  batchSize: 5000,
  canvasRef: { current: null },
  canvasOffsetX: 0,
  canvasOffsetY: 0,
  canvasScale: DEFAULT_SCALE,
  aggregatedData: defaultAggregatedData,
  maxTime: 0,
  topography: { links: new Map(), nodes: new Map() },
  topographyLoaded: false,
}

export const GraphContext: Context<IGraphContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {}
});
export const useGraphContext = () => useContext(GraphContext);
