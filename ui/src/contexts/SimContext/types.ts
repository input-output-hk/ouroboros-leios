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
  bytesSent: number;
  bytesReceived: number;
  generated: { [type: string]: number };
  sent: { [type: string]: { count: number, bytes: number } };
  received: { [type: string]: { count: number, bytes: number } };
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
  slot: number;
  pipeline: number;
  headerBytes: number;
  txs: ISimulationTransaction[];
}

export interface ISimulationEndorsementBlock {
  id: string;
  slot: number;
  pipeline: number;
  bytes: number;
  ibs: ISimulationInputBlock[];
  ebs: ISimulationEndorsementBlock[];
}

export interface ISimulationCertificate {
  bytes: number;
  eb: ISimulationEndorsementBlock;
}

export interface ISimulationBlock {
  slot: number;
  txs: ISimulationTransaction[];
  headerBytes: number;
  cert: ISimulationCertificate | null;
}

export interface ISimulationAggregatedDataState {
  progress: number;
  nodes: Map<string, ISimulationAggregatedData>;
  global: ISimulationGlobalData;
  blocks: ISimulationBlock[],
  lastNodesUpdated: string[];
}

export interface ISimulationIntermediateInputBlock {
  slot: number;
  pipeline: number;
  headerBytes: number;
  txs: number[];
}

export interface ISimulationIntermediateEndorsementBlock {
  slot: number;
  pipeline: number;
  bytes: number;
  ibs: string[];
  ebs: string[];
}

export interface ISimulationIntermediateDataState {
  txs: ISimulationTransaction[];
  praosTxs: Set<number>;
  leiosTxs: Set<number>;
  ibs: Map<string, ISimulationIntermediateInputBlock>;
  ebs: Map<string, ISimulationIntermediateEndorsementBlock>;
  bytes: Map<string, number>,
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

export interface IScenario {
  name: string;
  topology: string;
  duration: number;
  trace: string;
}

export interface ISimContextState {
  allScenarios: IScenario[];
  activeScenario: string;
  graph: IGraphContextState;
  blocks: IBlocksContextState;
  activeTab: Tab;
  aggregatedData: ISimulationAggregatedDataState;
  maxTime: number;
  tracePath: string;
  topography: ITransformedNodeMap;
  topologyPath: string;
  topologyLoaded: boolean;
  batchSize: number;
}

export type TSimContextActions =
  | { type: "SET_SCENARIOS"; payload: IScenario[] }
  | { type: "SET_SCENARIO", payload: string }
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
  | { type: "RESET_TOPOLOGY", payload: string }
  | {
    type: "SET_TOPOLOGY", payload: {
      topologyPath: string;
      topology: ITransformedNodeMap
    }
  };

export interface ISimContext {
  state: ISimContextState;
  dispatch: Dispatch<TSimContextActions>;
}
