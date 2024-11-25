import {
  IServerMessage,
  ITransactionMessage,
  ITransformedNodeMap
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
  sentTxs: Set<number>;
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
  | { type: "SET_GENERATED_MESSSAGES", payload: Set<number> }
  | { type: "REMOVE_GENERATED_MESSAGE"; payload: number }
  | { type: "ADD_SENT_TX"; payload: number }
  | { type: "SET_SENT_TXS"; payload: Set<number> }
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
