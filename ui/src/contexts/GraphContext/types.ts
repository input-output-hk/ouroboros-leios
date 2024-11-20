import { IServerMessage, ITransactionMessage, ITransformedNodeMap } from "@/components/Graph/types";
import { Dispatch, MutableRefObject, RefObject, SetStateAction } from "react";

export enum ESpeedOptions {
  "1/10" = 0.1,
  "2/10" = 0.2,
  "3/10" = 0.03,
}

export interface IGraphContextState {
  canvasRef: RefObject<HTMLCanvasElement>;
  currentTime: number;
  generatedMessages: Set<number>;
  setGeneratedMessages: Dispatch<SetStateAction<Set<number>>>;
  intervalId: MutableRefObject<Timer | null>;
  maxTime: number;
  messages: IServerMessage[];
  playing: boolean;
  sentTxs: Set<string>;
  simulationStartTime: MutableRefObject<number>;
  simulationPauseTime: MutableRefObject<number>;
  speed: ESpeedOptions;
  topography: ITransformedNodeMap;
  topographyLoaded: boolean;
  transactions: Map<number, ITransactionMessage[]>;
  setMessages: Dispatch<SetStateAction<IServerMessage[]>>;
  setPlaying: Dispatch<SetStateAction<boolean>>;
  setSentTxs: Dispatch<SetStateAction<Set<string>>>;
  setSpeed: Dispatch<SetStateAction<ESpeedOptions>>;
  setMaxTime: Dispatch<SetStateAction<number>>;
  setTopography: Dispatch<SetStateAction<ITransformedNodeMap>>;
  setTopographyLoaded: Dispatch<SetStateAction<boolean>>;
  setTransactions: Dispatch<SetStateAction<Map<number, ITransactionMessage[]>>>;
  setCurrentTime: Dispatch<SetStateAction<number>>;
}
