// Web Worker that owns the Loki tail WebSocket and runs the parser chain
// off the main thread. The main thread's only job is to dispatch the
// already-typed event batches into the reducer, which keeps the WebSocket
// reader from falling behind Loki's internal tail buffer (the cause of the
// silent `dropped_entries` losses we observed when this was all on the
// main thread).

import { IServerMessage } from "@/components/Sim/types";
import { parseStreamValue, resetPendingState } from "./lokiParsers";

export type LokiWorkerRequest =
  | { type: "CONNECT"; lokiHost: string }
  | { type: "DISCONNECT" };

export type LokiConnectionState =
  | "Connecting"
  | "Connected"
  | "NotConnected";

export type LokiWorkerResponse =
  | { type: "CONNECTION_STATE"; state: LokiConnectionState }
  | { type: "EVENTS"; events: IServerMessage[] }
  | { type: "DROPPED"; count: number };

const QUERY =
  '{service="cardano-node"} |~ "BlockFetchServer|MsgBlock|CompletedBlockFetch|MsgLeiosBlock|MsgLeiosBlockTxs|LeiosBlockForged|TraceForgedBlock|TraceAdoptedBlock|LeiosBlockAnnounced|LeiosBlockCertified|MsgLeiosVotes|LeiosVoted"';
const MAX_RETRY_DELAY_MS = 30000;

let ws: WebSocket | null = null;
let cancelled = false;
let retryCount = 0;
let retryTimeoutId: ReturnType<typeof setTimeout> | null = null;

const post = (msg: LokiWorkerResponse) => postMessage(msg);

const closeSocket = () => {
  if (retryTimeoutId !== null) {
    clearTimeout(retryTimeoutId);
    retryTimeoutId = null;
  }
  if (ws) {
    ws.close();
    ws = null;
  }
};

const connect = (lokiHost: string) => {
  if (cancelled) return;
  const wsUrl = `ws://${lokiHost}/loki/api/v1/tail?query=${encodeURIComponent(QUERY)}&limit=5000`;
  console.log(`[lokiWorker] Connecting (attempt ${retryCount + 1}):`, wsUrl);
  post({ type: "CONNECTION_STATE", state: "Connecting" });

  ws = new WebSocket(wsUrl);

  ws.onopen = () => {
    retryCount = 0;
    post({ type: "CONNECTION_STATE", state: "Connected" });
  };

  ws.onmessage = (event) => {
    try {
      const data = JSON.parse(event.data);

      // Loki signals tail-buffer drops via this array. Surfacing the count
      // lets the UI tell apart "no event ever fired" from "event fired but
      // we lost it on the consumer side."
      if (Array.isArray(data.dropped_entries) && data.dropped_entries.length) {
        post({ type: "DROPPED", count: data.dropped_entries.length });
      }

      if (!Array.isArray(data.streams)) return;
      const events: IServerMessage[] = [];

      for (const stream of data.streams) {
        if (!Array.isArray(stream.values)) continue;
        for (const [tsNs, logLine] of stream.values as [string, string][]) {
          const ts = parseFloat(tsNs) / 1_000_000_000;
          const parsed = parseStreamValue(stream.stream, ts, logLine);
          if (parsed) events.push(parsed);
        }
      }

      if (events.length > 0) {
        post({ type: "EVENTS", events });
      }
    } catch (error) {
      console.error("[lokiWorker] Error processing Loki message:", error);
    }
  };

  const scheduleRetry = () => {
    if (cancelled) return;
    retryCount++;
    const delay = Math.min(1000 * Math.pow(2, retryCount - 1), MAX_RETRY_DELAY_MS);
    console.log(`[lokiWorker] Retrying in ${delay}ms (attempt ${retryCount})`);
    retryTimeoutId = setTimeout(() => {
      if (!cancelled) connect(lokiHost);
    }, delay);
  };

  ws.onerror = (error) => {
    console.error("[lokiWorker] WebSocket error:", error);
    scheduleRetry();
  };

  ws.onclose = (event) => {
    console.log("[lokiWorker] WebSocket closed:", event.code, event.reason);
    if (!cancelled) {
      scheduleRetry();
    } else {
      post({ type: "CONNECTION_STATE", state: "NotConnected" });
    }
  };
};

self.onmessage = (e: MessageEvent<LokiWorkerRequest>) => {
  const req = e.data;
  if (req.type === "CONNECT") {
    cancelled = false;
    retryCount = 0;
    resetPendingState();
    closeSocket();
    connect(req.lokiHost);
  } else if (req.type === "DISCONNECT") {
    cancelled = true;
    closeSocket();
    post({ type: "CONNECTION_STATE", state: "NotConnected" });
  }
};
