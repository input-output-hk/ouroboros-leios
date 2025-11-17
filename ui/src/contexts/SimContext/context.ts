"use client";
import { Context, createContext, useContext } from "react";
import {
  ISimContext,
  ISimContextState,
  ISimulationAggregatedDataState,
  Tab,
} from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  progress: 0,
  nodes: new Map(),
  global: {
    praosTxOnChain: 0,
    leiosTxOnChain: 0,
  },
  blocks: [],
  transactions: [],
  lastNodesUpdated: [],
};

export const defaultState: ISimContextState = {
  allScenarios: [],
  activeScenario: "",
  aggregated: true,
  graph: {
    canvasRef: { current: null },
    canvasOffsetX: 0,
    canvasOffsetY: 0,
    canvasScale: 6,
  },
  blocks: {},
  activeTab: Tab.Graph,
  events: [],
  currentTime: 0,
  batchSize: 5000,
  speedMultiplier: 10,
  aggregatedData: defaultAggregatedData,
  maxTime: 0,
  tracePath: "",
  topography: { links: new Map(), nodes: new Map() },
  topologyPath: "",
  topologyLoaded: false,
};

export const SimContext: Context<ISimContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {},
});
export const useSimContext = () => useContext(SimContext);
