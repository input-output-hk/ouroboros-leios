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
  "127.0.0.1:3001": "UpstreamNode",
  "127.0.0.1:3002": "Node0",
  "127.0.0.1:3003": "DownstreamNode",
  // Add more mappings as needed
};

const parseRankingBlockSent = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=BlockFetch.Server.SendBlock
    // {"block":"56515bfd5751ca2c1ca0f21050cdb1cd020e396c623a16a2274528f643d4b5fd","kind":"BlockFetchServer","peer":{"connectionId":"127.0.0.1:3002 127.0.0.1:3003"}}
    if (log.kind === "BlockFetchServer" && log.peer && log.block) {
      const sender = streamLabels.process;
      const connectionId = log.peer.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0,
        id: `rb-${log.block.substring(0, 8)}`,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }

    // From immdb-server (no ns)
    // {"at":"2025-12-05T12:45:21.0021Z","connectionId":"127.0.0.1:3001 127.0.0.1:3002","direction":"Send","msg":"MsgBlock","mux_at":"2025-12-05T12:45:21.0020Z","prevCount":13}
    if (log.msg === "MsgBlock" && log.direction === "Send") {
      const sender = streamLabels.process;
      const connectionId = log.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: log.prevCount || 0,
        id: `rb-upstream-${log.prevCount + 1}`,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse RankingBlockSent log line:", logLine, error);
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
      const connectionId = log.peer.connectionId;
      let sender = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const senderEndpoint = endpoints[1];
          sender = HOST_PORT_TO_NODE[senderEndpoint] || sender;
        }
      }

      const message: IRankingBlockReceived = {
        type: EServerMessageType.RBReceived,
        slot: 0, // FIXME: use proper slot
        id: `rb-${log.block.substring(0, 8)}`,
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
    // {"at":"2025-12-05T12:45:20.9134Z","connectionId":"127.0.0.1:3001 127.0.0.1:3002","direction":"Send","msg":"MsgLeiosBlock","mux_at":"2025-12-05T12:45:20.9131Z","prevCount":0}
    if (log.msg === "MsgLeiosBlock" && log.direction === "Send") {
      const sender = streamLabels.process;
      const connectionId = log.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IEndorserBlockSent = {
        type: EServerMessageType.EBSent,
        slot: 0, // FIXME: use correct slot
        id: `eb-${log.prevCount || 0}`,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }

    // From cardano-node ns=LeiosFetch.Remote.Send.Block
    // {"kind":"Send","msg":{"eb":"\u003celided\u003e","ebBytesSize":27471,"kind":"MsgLeiosBlock"},"mux_at":"2025-12-05T12:45:20.93446848Z","peer":{"connectionId":"127.0.0.1:3002 127.0.0.1:3003"}}
    if (log.kind === "Send" && log.msg && log.msg.kind === "MsgLeiosBlock") {
      const sender = streamLabels.process;
      const connectionId = log.peer?.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IEndorserBlockSent = {
        type: EServerMessageType.EBSent,
        slot: 0, // FIXME: use correct slot
        id: `eb-${log.msg.eb}`, // FIXME: msg.eb is always elided
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse EndorserBlockSent log line:", logLine, error);
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
    // {"mux_at":"2025-12-05T12:45:21.98320066Z","peer":{"connectionId":"127.0.0.1:3003 127.0.0.1:3002"},"kind":"Recv","msg":{"kind":"MsgLeiosBlock","eb":"\u003celided\u003e","ebBytesSize":27471}}
    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlock") {
      const recipient = streamLabels.process;
      const connectionId = log.peer?.connectionId;
      let sender = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const senderEndpoint = endpoints[1];
          sender = HOST_PORT_TO_NODE[senderEndpoint] || sender;
        }
      }

      const message: IEndorserBlockReceived = {
        type: EServerMessageType.EBReceived,
        slot: 0, // FIXME: use correct slot
        id: `eb-${log.msg.eb}`, // FIXME: msg.eb is always elided
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
    // {"at":"2025-12-05T14:06:12.4254Z","connectionId":"127.0.0.1:3001 127.0.0.1:3002","direction":"Send","msg":"MsgLeiosBlockTxs","mux_at":"2025-12-05T14:06:12.4254Z","prevCount":265}
    if (log.msg === "MsgLeiosBlockTxs" && log.direction === "Send") {
      const sender = streamLabels.process;
      const connectionId = log.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: ITransactionSent = {
        type: EServerMessageType.TransactionSent,
        id: `tx-batch-${log.prevCount}`,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }

    // From cardano-node ns=LeiosFetch.Remote.Send.BlockTxs
    // {"kind":"Send","msg":{"kind":"MsgLeiosBlockTxs","numTxs":30,"txs":"\u003celided\u003e","txsBytesSize":491520},"mux_at":"2025-12-05T14:06:12.52467535Z","peer":{"connectionId":"127.0.0.1:3002 127.0.0.1:3003"}}
    if (log.kind === "Send" && log.msg && log.msg.kind === "MsgLeiosBlockTxs") {
      const sender = streamLabels.process;
      const connectionId = log.peer?.connectionId;
      let recipient = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

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
    console.warn("Failed to parse TransactionSent log line:", logLine, error);
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
      const connectionId = log.peer?.connectionId;
      let sender = "Node0";

      if (connectionId) {
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const senderEndpoint = endpoints[1];
          sender = HOST_PORT_TO_NODE[senderEndpoint] || sender;
        }
      }

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
                    console.warn("Parsed", event.time_s, event.message);
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
