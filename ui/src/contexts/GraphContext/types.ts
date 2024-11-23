import {
  IServerMessage,
  ITransactionMessage,
  ITransformedNodeMap,
} from "@/components/Graph/types";
import { Dispatch, MutableRefObject, RefObject } from "react";

export enum ESpeedOptions {
  "1/10" = 0.01,
  "2/10" = 0.02,
  "3/10" = 0.03,
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  currentTime: number;
  generatedMessages: Set<number>;
  intervalId: MutableRefObject<Timer | null>;
  maxTime: number;
  messages: Map<number, IServerMessage>;
  playing: boolean;
  sentTxs: Set<string>;
  simulationStartTime: MutableRefObject<number>;
  simulationPauseTime: MutableRefObject<number>;
  speed: ESpeedOptions;
  topography: ITransformedNodeMap;
  topographyLoaded: boolean;
  transactions: Map<number, ITransactionMessage[]>;
}

export type TGraphContextActions =
  | { type: "SET_CURRENT_TIME"; payload: number }
  | { type: "ADD_GENERATED_MESSAGE"; payload: number }
  | { type: "REMOVE_GENERATED_MESSAGE"; payload: number }
  | { type: "SET_MAX_TIME"; payload: number }
  | { type: "ADD_MESSAGE"; payload: IServerMessage }
  | { type: "ADD_MESSAGES"; payload: Map<number, IServerMessage> }
  | { type: "REMOVE_MESSAGE"; payload: number }
  | { type: "REMOVE_MESSAGES"; payload: number[] }
  | { type: "SET_PLAYING"; payload: boolean }
  | { type: "TOGGLE_PLAYING" }
  | { type: "ADD_SENT_TX"; payload: string }
  | { type: "REMOVE_SENT_TX"; payload: string }
  | { type: "SET_SPEED"; payload: ESpeedOptions }
  | { type: "SET_TOPOGRAPHY"; payload: ITransformedNodeMap }
  | { type: "SET_TOPOGRAPHY_LOADED"; payload: boolean }
  | {
      type: "SET_TRANSACTIONS";
      payload: Map<number, ITransactionMessage[]>;
    }
  | {
    type: "REMOVE_TRANSACTION";
    payload: number;
  }
  | {
    type: "BATCH_UPDATE";
    payload: Partial<IGraphContextState>;
  }
  | { type: "RESET_STATE" };

export interface IGraphContext {
  state: IGraphContextState;
  dispatch: Dispatch<TGraphContextActions>;
}
