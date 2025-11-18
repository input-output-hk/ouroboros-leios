import { IServerMessage, ITransformedNodeMap } from "@/components/Sim/types";
import { Dispatch, RefObject } from "react";

export enum ESpeedOptions {
  "1% Speed" = 0.01,
  "3% Speed" = 0.03,
  "10% Speed" = 0.1,
}


export interface ISimulationAggregatedData {
  bytesSent: number;
  bytesReceived: number;
  generated: { [type: string]: number };
  sent: { [type: string]: { count: number; bytes: number } };
  received: { [type: string]: { count: number; bytes: number } };
}

export interface ISimulationGlobalData {
  praosTxOnChain: number;
  leiosTxOnChain: number;
}

export interface ISimulationTransactionData {
  timestamp: number;
  created: number;
  inIb: number;
  inEb: number;
  onChain: number;
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
  txs: ISimulationTransaction[];
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
  blocks: ISimulationBlock[];
  transactions: ISimulationTransactionData[];
  lastNodesUpdated: string[];
  eventCounts: {
    total: number;
    byType: Record<string, number>;
  };
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
  txs: string[];
  ibs: string[];
  ebs: string[];
}

type TxStatus = "created" | "inIb" | "inEb" | "onChain";

export interface ISimulationIntermediateDataState {
  txs: ISimulationTransaction[];
  txStatuses: TxStatus[];
  praosTxs: Set<number>;
  leiosTxs: Set<number>;
  ibs: Map<string, ISimulationIntermediateInputBlock>;
  ebs: Map<string, ISimulationIntermediateEndorsementBlock>;
  bytes: Map<string, number>;
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement | null>;
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
  Transactions,
}

export interface IScenario {
  name: string;
  topology: string;
  duration: number;
  trace: string;
  aggregated: boolean;
}

export interface ISimContextState {
  allScenarios: IScenario[];
  activeScenario: string;
  graph: IGraphContextState;
  blocks: IBlocksContextState;
  activeTab: Tab;
  aggregatedData: ISimulationAggregatedDataState;
  tracePath: string;
  aggregated: boolean;
  topography: ITransformedNodeMap;
  topologyPath: string;
  topologyLoaded: boolean;
  events: IServerMessage[];
  currentTime: number;
  maxTime: number;
  isPlaying: boolean;
  speedMultiplier: number;
}

export type TSimContextActions =
  | { type: "SET_SCENARIOS"; payload: IScenario[] }
  | { type: "SET_SCENARIO"; payload: string }
  | { type: "SET_ACTIVE_TAB"; payload: Tab }
  | { type: "SET_CURRENT_NODE"; payload: string | undefined }
  | { type: "SET_CURRENT_BLOCK"; payload: number | undefined }
  | {
      type: "SET_SPEED";
      payload: {
        speedMultiplier: number;
      };
    }
  | {
      type: "SET_CANVAS_PROPS";
      payload: Partial<{
        canvasScale: ((prev: number) => number) | number;
        canvasOffsetX: ((prev: number) => number) | number;
        canvasOffsetY: ((prev: number) => number) | number;
      }>;
    }
  // TODO: unused
  | { type: "SET_AGGREGATED_DATA"; payload: ISimulationAggregatedDataState }
  | {
      type: "BATCH_UPDATE";
      payload: Partial<ISimContextState>;
    }
  | { type: "RESET_TOPOLOGY"; payload: string }
  | {
      type: "SET_TOPOLOGY";
      payload: {
        topologyPath: string;
        topology: ITransformedNodeMap;
      };
    }
  | {
      type: "ADD_TIMELINE_EVENT";
      payload: IServerMessage;
    }
  | {
      type: "ADD_TIMELINE_EVENT_BATCH";
      payload: IServerMessage[];
    }
  | { type: "SET_TIMELINE_TIME"; payload: number }
  | { type: "SET_TIMELINE_PLAYING"; payload: boolean }
  | { type: "SET_TIMELINE_SPEED"; payload: number }
  | { type: "RESET_TIMELINE" };

export interface ISimContext {
  state: ISimContextState;
  dispatch: Dispatch<TSimContextActions>;
}
