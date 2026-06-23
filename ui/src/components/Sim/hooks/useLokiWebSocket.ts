// Thin lifecycle wrapper around the Loki tail worker. The worker owns the
// WebSocket and the parser pipeline; this hook just dispatches the parsed
// event batches into the reducer and tracks the Loki-reported drop count.

import { useSimContext } from "@/contexts/SimContext/context";
import { EConnectionState } from "@/contexts/SimContext/types";
import { useRef } from "react";
import type {
  LokiConnectionState,
  LokiWorkerResponse,
} from "./lokiWorker";

const CONNECTION_STATE_MAP: Record<LokiConnectionState, EConnectionState> = {
  Connecting: EConnectionState.Connecting,
  Connected: EConnectionState.Connected,
  NotConnected: EConnectionState.NotConnected,
};

const spawnWorker = (lokiHost: string, dispatch: any) => {
  const worker = new Worker(new URL("./lokiWorker.ts", import.meta.url), {
    type: "module",
  });

  let hasAutoStartedPlayback = false;

  worker.onmessage = (e: MessageEvent<LokiWorkerResponse>) => {
    const msg = e.data;
    if (msg.type === "CONNECTION_STATE") {
      dispatch({
        type: "SET_LOKI_CONNECTION_STATE",
        payload: CONNECTION_STATE_MAP[msg.state],
      });
    } else if (msg.type === "EVENTS") {
      dispatch({ type: "ADD_TIMELINE_EVENT_BATCH", payload: msg.events });
      if (!hasAutoStartedPlayback) {
        hasAutoStartedPlayback = true;
        dispatch({ type: "SET_TIMELINE_PLAYING", payload: true });
      }
    } else if (msg.type === "DROPPED") {
      dispatch({ type: "ADD_LOKI_DROPPED_ENTRIES", payload: msg.count });
    }
  };

  worker.onerror = (error) => {
    console.error("[useLokiWebSocket] worker error:", error);
  };

  worker.postMessage({ type: "CONNECT", lokiHost });
  return worker;
};

export const useLokiWebSocket = () => {
  const {
    state: { lokiHost, lokiConnectionState },
    dispatch,
  } = useSimContext();

  const workerRef = useRef<Worker | null>(null);

  const connect = () => {
    if (!lokiHost || lokiConnectionState === EConnectionState.Connected) return;
    dispatch({ type: "RESET_TIMELINE" });
    workerRef.current = spawnWorker(lokiHost, dispatch);
  };

  const disconnect = () => {
    if (workerRef.current) {
      workerRef.current.postMessage({ type: "DISCONNECT" });
      workerRef.current.terminate();
      workerRef.current = null;
    }
    dispatch({
      type: "SET_LOKI_CONNECTION_STATE",
      payload: EConnectionState.NotConnected,
    });
  };

  return { connect, disconnect };
};
