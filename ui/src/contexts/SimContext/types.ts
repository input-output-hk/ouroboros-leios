import {
  ITransformedNodeMap
} from "@/components/Sim/types";
import { Dispatch, RefObject } from "react";

export enum ESpeedOptions {
  "1% Speed" = 0.01,
  "3% Speed" = 0.03,
  "10% Speed" = 0.1,
}

export interface ISimulationAggregatedTotalData {
  txGenerated: number;
  txPropagations: number;
  ibGenerated: number;
  ibPropagations: number;
  ebGenerated: number;
  ebPropagations: number;
  pbGenerated: number;
  pbPropagations: number;
  votesGenerated: number;
  votesPropagations: number;
  praosTxOnChain: number;
  leiosTxOnChain: number;
}

export interface ISimulationAggregatedData {
  txGenerated: number;
  txSent: number;
  txReceived: number;
  ibGenerated: number;
  ibSent: number;
  ibReceived: number;
  ebGenerated: number;
  ebSent: number;
  ebReceived: number;
  pbGenerated: number;
  pbSent: number;
  pbReceived: number;
  votesGenerated: number;
  votesReceived: number;
  votesSent: number;
}

export interface ISimulationGlobalData {
  praosTxOnChain: number;
  leiosTxOnChain: number;
}

export interface ISimulationTransaction {
  id: number;
  bytes: number;
}

export interface ISimulationInputBlock {
  id: string;
  txs: ISimulationTransaction[];
}

export interface ISimulationEndorsementBlock {
  id: string;
  ibs: ISimulationInputBlock[];
}

export interface ISimulationBlock {
  slot: number;
  txs: ISimulationTransaction[];
  endorsement: ISimulationEndorsementBlock | null;
}

export interface ISimulationAggregatedDataState {
  progress: number;
  nodes: Map<string, ISimulationAggregatedData>;
  global: ISimulationGlobalData;
  blocks: ISimulationBlock[],
  lastNodesUpdated: string[];
}

export interface ISimulationIntermediateDataState {
  txs: ISimulationTransaction[];
  ibTxs: Map<string, number[]>;
  ebIbs: Map<string, string[]>;
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  canvasScale: number;
  canvasOffsetX: number;
  canvasOffsetY: number;
  currentNode?: string;
}

export interface IBlocksContextState {
  currentBlock?: number;
}

export enum Tab {
  Graph,
  Blocks,
}

export interface ISimContextState {
  graph: IGraphContextState;
  blocks: IBlocksContextState;
  activeTab: Tab;
  aggregatedData: ISimulationAggregatedDataState;
  maxTime: number;
  topography: ITransformedNodeMap;
  topographyLoaded: boolean;
  batchSize: number;
}

export type TSimContextActions =
  | { type: "SET_ACTIVE_TAB"; payload: Tab }
  | { type: "SET_CURRENT_NODE"; payload: string | undefined }
  | { type: "SET_CURRENT_BLOCK"; payload: number | undefined }
  | { type: "SET_BATCH_SIZE"; payload: number }
  | {
    type: "SET_CANVAS_PROPS"; payload: Partial<{
      canvasScale: ((prev: number) => number) | number,
      canvasOffsetX: ((prev: number) => number) | number,
      canvasOffsetY: ((prev: number) => number) | number
    }>
  }
  | { type: "SET_AGGREGATED_DATA"; payload: ISimulationAggregatedDataState }
  | {
    type: "BATCH_UPDATE";
    payload: Partial<ISimContextState>;
  }
  | { type: "RESET_STATE" };

export interface ISimContext {
  state: ISimContextState;
  dispatch: Dispatch<TSimContextActions>;
}
