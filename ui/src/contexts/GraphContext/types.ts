import {
  IServerMessage,
  ITransformedNodeMap
} from "@/components/Graph/types";
import { Dispatch, MutableRefObject, RefObject } from "react";

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
}

export interface ISimulationAggregatedDataState {
  nodes: Map<string, ISimulationAggregatedData>;
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  currentTime: number;
  currentNode?: string;
  generatedMessages: number[];
  intervalId: MutableRefObject<Timer | undefined>;
  aggregatedData: MutableRefObject<ISimulationAggregatedDataState>;
  maxTime: number;
  messages: Map<number, IServerMessage>;
  playing: boolean;
  sentTxs: number[];
  simulationStartTime: MutableRefObject<number>;
  simulationPauseTime: MutableRefObject<number>;
  speed: ESpeedOptions;
  topography: ITransformedNodeMap;
  topographyLoaded: boolean;
}

export type TGraphContextActions =
  | { type: "SET_CURRENT_TIME"; payload: number }
  | { type: "SET_CURRENT_NODE"; payload: string | undefined }
  | { type: "ADD_GENERATED_MESSAGE"; payload: number }
  | { type: "SET_GENERATED_MESSSAGES", payload: number[] }
  | { type: "REMOVE_GENERATED_MESSAGE"; payload: number }
  | { type: "ADD_SENT_TX"; payload: number }
  | { type: "SET_SENT_TXS"; payload: number[] }
  | { type: "REMOVE_SENT_TX"; payload: number }
  | { type: "SET_PLAYING"; payload: boolean }
  | { type: "TOGGLE_PLAYING" }
  | { type: "SET_SPEED"; payload: ESpeedOptions }
  | {
    type: "BATCH_UPDATE";
    payload: Partial<IGraphContextState>;
  }
  | { type: "RESET_STATE" };

export interface IGraphContext {
  state: IGraphContextState;
  dispatch: Dispatch<TGraphContextActions>;
}
