"use client";
import { Context, createContext, useContext } from "react";
import { IGraphContext, IGraphContextState, ISimulationAggregatedDataState } from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  progress: 0,
  nodes: new Map()
};

export const defaultState: IGraphContextState = {
  canvasRef: { current: null },
  canvasOffsetX: 0,
  canvasOffsetY: 0,
  canvasScale: 4,
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
