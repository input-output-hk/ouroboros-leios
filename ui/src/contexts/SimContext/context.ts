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
  messages: [],
  eventCounts: {
    total: 0,
    byType: {},
  },
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
  aggregatedData: defaultAggregatedData,
  tracePath: "",
  topography: { links: new Map(), nodes: new Map() },
  topologyPath: "",
  topologyLoaded: false,
  events: [],
  currentTime: 0,
  maxTime: 0,
  isPlaying: false,
  speedMultiplier: 1,
};

export const SimContext: Context<ISimContext> = createContext({
  state: defaultState,
  dispatch: (_val) => {},
});
export const useSimContext = () => useContext(SimContext);
