import {
  ITransformedNodeMap
} from "@/components/Graph/types";
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
  progress: number;
  nodes: Map<string, ISimulationAggregatedData>;
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  canvasScale: number;
  canvasOffsetX: number;
  canvasOffsetY: number;
  currentNode?: string;
  aggregatedData: ISimulationAggregatedDataState;
  maxTime: number;
  topography: ITransformedNodeMap;
  topographyLoaded: boolean;
}

export type TGraphContextActions =
  | { type: "SET_CURRENT_NODE"; payload: string | undefined }
  | { type: "SET_CANVAS_PROPS"; payload: Partial<{
    canvasScale: ((prev: number) => number) | number,
    canvasOffsetX: ((prev: number) => number) | number,
    canvasOffsetY: ((prev: number) => number) | number
  } }
  | { type: "SET_AGGREGATED_DATA"; payload: ISimulationAggregatedDataState }
  | {
    type: "BATCH_UPDATE";
    payload: Partial<IGraphContextState>;
  }
  | { type: "RESET_STATE" };

export interface IGraphContext {
  state: IGraphContextState;
  dispatch: Dispatch<TGraphContextActions>;
}
