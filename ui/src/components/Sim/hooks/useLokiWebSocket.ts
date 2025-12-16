import { useSimContext } from "@/contexts/SimContext/context";
import {
  IServerMessage,
  EServerMessageType,
  IRankingBlockSent,
  IRankingBlockReceived,
  IEndorserBlockSent,
  IEndorserBlockReceived,
  ITransactionSent,
  ITransactionReceived,
} from "@/components/Sim/types";
import { useRef } from "react";
import { EConnectionState } from "@/contexts/SimContext/types";

// FIXME: latency in topology is wrong

// TODO: Replace with topology-based mapping
const HOST_PORT_TO_NODE: Record<string, string> = {
  "10.0.0.1:3001": "UpstreamNode",
  "10.0.0.2:3002": "Node0",
  "10.0.0.3:3003": "DownstreamNode",
  // Add more mappings as needed
};

const getRemoteFromConnection = (connectionId: string | undefined): string => {
  if (!connectionId) return "UNKNOWN";

  const endpoints = connectionId.split(" ");
  if (endpoints.length === 2) {
    const targetEndpoint = endpoints[1];
    return HOST_PORT_TO_NODE[targetEndpoint] || "UNKNOWN";
  }

  return "UNKNOWN";
};

const parseRankingBlockSent = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=BlockFetch.Server.SendBlock
    // {"block": "23b021f8e2c06e64b10647d9eeb5c9f11e50181f5a569424e49f2448f6d5f8a8", "kind": "BlockFetchServer", "peer": {"connectionId": "10.0.0.2:3002 10.0.0.3:3003"}}
    if (log.kind === "BlockFetchServer" && log.peer && log.block) {
      const sender = streamLabels.process;
      const recipient = getRemoteFromConnection(log.peer.connectionId);

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0,
        id: log.block,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }

    // From immdb-server (no ns)
    // {"at":"2025-12-16T11:35:30.0472Z","connectionId":"0.0.0.0:3001 10.0.0.2:3002","direction":"Send","msg":{"blockHash":"23b021f8e2c06e64b10647d9eeb5c9f11e50181f5a569424e49f2448f6d5f8a8","kind":"MsgBlock"},"mux_at":null,"prevCount":0}
    if (log.direction === "Send" && log.msg && log.msg.kind === "MsgBlock") {
      const sender = streamLabels.process;
      const recipient = getRemoteFromConnection(log.connectionId);

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0,
        id: log.msg.blockHash,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.error("Failed to parse RankingBlockSent log line:", logLine, error);
  }

  return null;
};

const parseRankingBlockReceived = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // ns=BlockFetch.Client.CompletedBlockFetch
    // {"block":"56515bfd5751ca2c1ca0f21050cdb1cd020e396c623a16a2274528f643d4b5fd","delay":4985924.003937032,"kind":"CompletedBlockFetch","peer":{"connectionId":"127.0.0.1:3003 127.0.0.1:3002"},"size":862}
    if (log.kind === "CompletedBlockFetch" && log.peer && log.block) {
      const recipient = streamLabels.process;
      const sender = getRemoteFromConnection(log.peer.connectionId);

      const message: IRankingBlockReceived = {
        type: EServerMessageType.RBReceived,
        slot: 0, // FIXME: use proper slot
        id: log.block,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn(
      "Failed to parse RankingBlockReceived log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseEndorserBlockSent = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From immdb-server (no ns)
    // {"at": "2025-12-15T14:20:07.5401Z", "connectionId": "0.0.0.0:3001 10.0.0.2:3002", "direction": "Send", "msg": {"ebBytesSize": 27471, "ebHash": "8f5ef7199fd1d75c7a98f6e4f53987380ed3897b132f499e0715ae93c225400c", "kind": "MsgLeiosBlock"}, "mux_at": "2025-12-15T14:20:07.5399Z", "prevCount": 0}
    // From cardano-node ns=LeiosFetch.Remote.Send.Block
    // {"kind": "Send", "msg": {"ebBytesSize": 27471, "ebHash": "8f5ef7199fd1d75c7a98f6e4f53987380ed3897b132f499e0715ae93c225400c", "kind": "MsgLeiosBlock"}, "mux_at": "2025-12-15T14:20:08.12367307Z", "peer": {"connectionId": "10.0.0.2:3002 10.0.0.3:3003"}}
    if (
      (log.direction || log.kind) === "Send" &&
      log.msg &&
      log.msg.kind === "MsgLeiosBlock"
    ) {
      const sender = streamLabels.process;
      const recipient = getRemoteFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IEndorserBlockSent = {
        type: EServerMessageType.EBSent,
        slot: 0, // FIXME: drop as not available/needed
        id: log.msg.ebHash,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.error(
      "Failed to parse EndorserBlockSent log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseEndorserBlockReceived = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=LeiosFetch.Remote.Receive.Block
    // {"kind":"Recv","msg":{"ebBytesSize":27471,"ebHash":"320648bc67a2a160bda3ca52cdf1fe05b3cee404da82fb98e5fa02b2fb970741","kind":"MsgLeiosBlock"},"mux_at":"2025-12-15T15:18:49.13935251Z","peer":{"connectionId":"10.0.0.2:3002 10.0.0.1:3001"}}
    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlock") {
      const recipient = streamLabels.process;
      const sender = getRemoteFromConnection(log.peer.connectionId);

      const message: IEndorserBlockReceived = {
        type: EServerMessageType.EBReceived,
        slot: 0, // FIXME: use correct slot
        id: log.msg.ebHash,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn(
      "Failed to parse EndorserBlockReceived log line:",
      logLine,
      error,
    );
  }

  return null;
};

const parseTransactionSent = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // TODO: indicate this is many transactions or visualize as a very big transaction

    // From immdb-server (no ns)
    // {"at":"2025-12-15T15:19:01.5108Z","connectionId":"0.0.0.0:3001 10.0.0.2:3002","direction":"Send","msg":{"kind":"MsgLeiosBlockTxs","numTxs":30,"txs":"<elided>","txsBytesSize":491520},"mux_at":"2025-12-15T15:19:01.5107Z","prevCount":235}
    // From cardano-node ns=LeiosFetch.Remote.Send.BlockTxs
    // {"kind":"Send","msg":{"kind":"MsgLeiosBlockTxs","numTxs":30,"txs":"\u003celided\u003e","txsBytesSize":491520},"mux_at":"2025-12-05T14:06:12.52467535Z","peer":{"connectionId":"127.0.0.1:3002 127.0.0.1:3003"}}
    if (
      (log.direction || log.kind) === "Send" &&
      log.msg &&
      log.msg.kind === "MsgLeiosBlockTxs"
    ) {
      const sender = streamLabels.process;
      const recipient = getRemoteFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: ITransactionSent = {
        type: EServerMessageType.TransactionSent,
        id: `tx-batch-${log.msg.txs}`, // FIXME: msg.txs is always elided
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.error("Failed to parse TransactionSent log line:", logLine, error);
  }

  return null;
};

const parseTransactionReceived = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=LeiosFetch.Remote.Receive.BlockTxs
    // {"mux_at":"2025-12-05T14:06:12.52499731Z","peer":{"connectionId":"127.0.0.1:3003 127.0.0.1:3002"},"kind":"Recv","msg":{"txsBytesSize":491520,"kind":"MsgLeiosBlockTxs","numTxs":30,"txs":"\u003celided\u003e"}}
    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlockTxs") {
      const recipient = streamLabels.process;
      const sender = getRemoteFromConnection(log.peer?.connectionId);

      const message: ITransactionReceived = {
        type: EServerMessageType.TransactionReceived,
        id: `tx-${log.msg.txs}`, // FIXME: msg.txs is always elided
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn(
      "Failed to parse TransactionReceived log line:",
      logLine,
      error,
    );
  }

  return null;
};

function connectLokiWebSocket(lokiHost: string, dispatch: any): () => void {
  // NOTE: Single websocket is essential because:
  // 1. Timeline aggregation assumes events are chronologically ordered
  // 2. Multiple websockets deliver events out of order across different queries
  // 3. Loki naturally returns results in chronological order within a single stream
  // 4. Sorting large event arrays in the reducer is too expensive for dense simulation data
  const query =
    '{service="cardano-node"} |~ "BlockFetchServer|MsgBlock|CompletedBlockFetch|MsgLeiosBlock|MsgLeiosBlockTxs"';
  const wsUrl = `ws://${lokiHost}/loki/api/v1/tail?query=${encodeURIComponent(query)}&limit=5000`;

  let hasAutoStartedPlayback = false;
  let ws: WebSocket | null = null;
  let retryTimeoutId: number | null = null;
  let cancelled = false;
  let retryCount = 0;
  const maxRetryDelay = 30000; // 30 seconds max delay

  const connect = () => {
    if (cancelled) return;

    console.log(`Connecting to Loki (attempt ${retryCount + 1}):`, wsUrl);
    dispatch({
      type: "SET_LOKI_CONNECTION_STATE",
      payload: EConnectionState.Connecting,
    });

    ws = new WebSocket(wsUrl);

    ws.onopen = () => {
      retryCount = 0; // Reset retry count on successful connection
      dispatch({
        type: "SET_LOKI_CONNECTION_STATE",
        payload: EConnectionState.Connected,
      });
    };

    let count = 0;
    ws.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        console.debug("Received Loki streams:", data);

        if (data.streams && Array.isArray(data.streams)) {
          const events: IServerMessage[] = [];

          data.streams.forEach((stream: any) => {
            console.debug("Stream labels:", stream.stream);
            if (stream.values && Array.isArray(stream.values)) {
              stream.values.forEach(
                ([timestamp, logLine]: [string, string]) => {
                  count++;
                  console.debug(`Stream value:`, count, { timestamp, logLine });
                  const ts = parseFloat(timestamp) / 1000000000;

                  // TODO: simplify and push further upstream (e.g. into alloy)
                  const event =
                    parseRankingBlockSent(stream.stream, ts, logLine) ||
                    parseRankingBlockReceived(stream.stream, ts, logLine) ||
                    parseEndorserBlockSent(stream.stream, ts, logLine) ||
                    parseEndorserBlockReceived(stream.stream, ts, logLine) ||
                    parseTransactionSent(stream.stream, ts, logLine) ||
                    parseTransactionReceived(stream.stream, ts, logLine);
                  if (event) {
                    console.warn(
                      "Parsed",
                      event.time_s,
                      event.message,
                      "from",
                      logLine,
                    );
                    events.push(event);
                  }
                },
              );
            }
          });

          if (events.length > 0) {
            dispatch({ type: "ADD_TIMELINE_EVENT_BATCH", payload: events });

            // Auto-start playback on first batch of events
            if (!hasAutoStartedPlayback) {
              hasAutoStartedPlayback = true;
              dispatch({ type: "SET_TIMELINE_PLAYING", payload: true });
            }
          }
        }
      } catch (error) {
        console.error("Error processing Loki message:", error);
      }
    };

    const scheduleRetry = () => {
      if (cancelled) return;

      retryCount++;
      // Exponential backoff: 1s, 2s, 4s, 8s, 16s, 30s (max)
      const delay = Math.min(1000 * Math.pow(2, retryCount - 1), maxRetryDelay);
      console.log(`Retrying connection in ${delay}ms (attempt ${retryCount})`);

      retryTimeoutId = window.setTimeout(() => {
        if (!cancelled) {
          connect();
        }
      }, delay);
    };

    ws.onerror = (error) => {
      console.error("WebSocket error:", error);
      scheduleRetry();
    };

    ws.onclose = (event) => {
      console.log("WebSocket closed:", event.code, event.reason);
      if (!cancelled) {
        scheduleRetry();
      } else {
        dispatch({
          type: "SET_LOKI_CONNECTION_STATE",
          payload: EConnectionState.NotConnected,
        });
      }
    };
  };

  // Start initial connection
  connect();

  return () => {
    cancelled = true;
    if (retryTimeoutId) {
      clearTimeout(retryTimeoutId);
      retryTimeoutId = null;
    }
    if (ws) {
      ws.close();
    }
    dispatch({
      type: "SET_LOKI_CONNECTION_STATE",
      payload: EConnectionState.NotConnected,
    });
  };
}

export const useLokiWebSocket = () => {
  const {
    state: { lokiHost, lokiConnectionState },
    dispatch,
  } = useSimContext();

  const cleanupRef = useRef<(() => void) | null>(null);

  const connect = () => {
    if (!lokiHost || lokiConnectionState === EConnectionState.Connected) return;

    dispatch({ type: "RESET_TIMELINE" });

    cleanupRef.current = connectLokiWebSocket(lokiHost, dispatch);
  };

  const disconnect = () => {
    cleanupRef.current?.();
    cleanupRef.current = null;
    dispatch({
      type: "SET_LOKI_CONNECTION_STATE",
      payload: EConnectionState.NotConnected,
    });
  };

  return { connect, disconnect };
};
