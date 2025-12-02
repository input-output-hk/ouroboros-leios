"use client";
import { Context, createContext, useContext } from "react";
import {
  ISimContext,
  ISimContextState,
  ISimulationAggregatedDataState,
} from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  nodes: new Map(),
  global: {
    praosTxOnChain: 0,
    leiosTxOnChain: 0,
  },
  lastNodesUpdated: [],
  messages: [],
  eventCounts: {
    total: 0,
    byType: {},
  },
  lastAggregatedTime: 0,
};

export const defaultState: ISimContextState = {
  allScenarios: [],
  activeScenario: "",
  graph: {
    canvasRef: { current: null },
    canvasOffsetX: 0,
    canvasOffsetY: 0,
    canvasScale: 6,
  },
  aggregatedData: defaultAggregatedData,
  tracePath: "",
  lokiHost: undefined,
  lokiConnected: false,
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
  dispatch: () => {},
} as ISimContext);
export const useSimContext = () => useContext(SimContext);
