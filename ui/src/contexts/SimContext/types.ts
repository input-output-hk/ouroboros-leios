import { IServerMessage, ITransformedNodeMap } from "@/components/Sim/types";
import { Dispatch, RefObject } from "react";

// Types of messages submitted between nodes
export enum EMessageType {
  EB = "eb",
  RB = "rb",
  TX = "tx",
  Votes = "votes",
}

export enum ActivityAction {
  Generated = "generated",
  Sent = "sent",
  Received = "received",
}

export interface ISimulationAggregatedData {
  bytesSent: number;
  bytesReceived: number;
  generated: Map<EMessageType, number>;
  sent: Map<EMessageType, { count: number; bytes: number }>;
  received: Map<EMessageType, { count: number; bytes: number }>;
  lastActivity?: {
    type: EMessageType;
    action: ActivityAction;
    time: number;
  };
}

export interface ISimulationGlobalData {
  praosTxOnChain: number;
  leiosTxOnChain: number;
}

export interface IMessageAnimation {
  id: string;
  type: EMessageType;
  sender: string;
  recipient: string;
  sentTime: number;
  receivedTime: number;
  progress: number; // 0-1, calculated based on current timeline position
}

export interface ISimulationAggregatedDataState {
  nodes: Map<string, ISimulationAggregatedData>;
  global: ISimulationGlobalData;
  lastNodesUpdated: string[];
  messages: IMessageAnimation[]; // Active messages traveling on the graph
  eventCounts: {
    total: number;
    byType: Record<string, number>;
  };
  lastAggregatedTime: number; // Timestamp up to which aggregation was last computed
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement | null>;
  canvasScale: number;
  canvasOffsetX: number;
  canvasOffsetY: number;
  currentNode?: string;
}

export interface IScenario {
  name: string;
  topology: string;
  duration: number;
  trace?: string;
  loki?: string;
}

export interface ISimContextState {
  allScenarios: IScenario[];
  activeScenario: string;
  autoStart: boolean;
  graph: IGraphContextState;
  aggregatedData: ISimulationAggregatedDataState;
  tracePath: string;
  lokiHost?: string;
  lokiConnected: boolean;
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
  | { type: "SET_SCENARIO"; payload: string; autoStart?: boolean }
  | { type: "SET_CURRENT_NODE"; payload: string | undefined }
  | {
      type: "SET_CANVAS_PROPS";
      payload: Partial<{
        canvasScale: ((prev: number) => number) | number;
        canvasOffsetX: ((prev: number) => number) | number;
        canvasOffsetY: ((prev: number) => number) | number;
      }>;
    }
  | { type: "BATCH_UPDATE"; payload: Partial<ISimContextState> }
  | { type: "RESET_TOPOLOGY"; payload: string }
  | {
      type: "SET_TOPOLOGY";
      payload: { topologyPath: string; topology: ITransformedNodeMap };
    }
  | { type: "ADD_TIMELINE_EVENT_BATCH"; payload: IServerMessage[] }
  | { type: "SET_TIMELINE_TIME"; payload: number }
  | { type: "SET_TIMELINE_PLAYING"; payload: boolean }
  | { type: "SET_TIMELINE_SPEED"; payload: number }
  | { type: "RESET_TIMELINE" }
  | { type: "SET_LOKI_CONNECTED"; payload: boolean };

export interface ISimContext {
  state: ISimContextState;
  dispatch: Dispatch<TSimContextActions>;
}
