"use client";
import { Context, createContext, useContext } from "react";
import {
  ISimContext,
  ISimContextState,
  ISimulationAggregatedDataState,
  EConnectionState,
} from "./types";

export const defaultAggregatedData: ISimulationAggregatedDataState = {
  nodes: new Map(),
  global: {
    praosTxOnChain: 0,
    leiosTxOnChain: 0,
  },
  messages: [],
  edges: new Map(),
  nodeActivity: new Map(),
  eventCounts: {
    total: 0,
    byType: {},
  },
  lastAggregatedTime: 0,
};

export const defaultState: ISimContextState = {
  allScenarios: [],
  activeScenario: "",
  autoStart: false,
  graph: {
    canvasRef: { current: null },
    canvasOffsetX: 0,
    canvasOffsetY: 0,
    canvasScale: 6,
  },
  aggregatedData: defaultAggregatedData,
  tracePath: "",
  lokiHost: undefined,
  lokiConnectionState: EConnectionState.NotConnected,
  topography: { links: new Map(), nodes: new Map() },
  topologyPath: "",
  topologyLoaded: false,
  events: [],
  currentTime: 0,
  minTime: 0,
  maxTime: 0,
  isPlaying: false,
  speedMultiplier: 1,
};

export const SimContext: Context<ISimContext> = createContext({
  state: defaultState,
  dispatch: () => {},
} as ISimContext);
export const useSimContext = () => useContext(SimContext);
