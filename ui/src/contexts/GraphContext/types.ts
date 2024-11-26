import {
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
  ITransformedNodeMap
} from "@/components/Graph/types";
import { Dispatch, MutableRefObject, RefObject } from "react";

export enum ESpeedOptions {
  "1% Speed" = 0.01,
  "3% Speed" = 0.03,
  "10% Speed" = 0.1,
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  transactionsByIdRef: MutableRefObject<Map<number, ITransactionMessage[]>>;
  txGeneratedMessagesById: MutableRefObject<Map<number, IServerMessage<ITransactionGenerated>>>;
  txSentMessagesById: MutableRefObject<Map<number, IServerMessage<ITransactionSent>[]>>;
  txReceivedMessagesById: MutableRefObject<Map<number, IServerMessage<ITransactionReceived>[]>>;
  currentTime: number;
  generatedMessages: number[];
  intervalId: MutableRefObject<number | null>;
  maxTime: number;
  messages: Map<number, IServerMessage>;
  playing: boolean;
  sentTxs: number[];
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
