import { useSimContext } from "@/contexts/SimContext/context";
import {
  IServerMessage,
  EServerMessageType,
  IRankingBlockGenerated,
  IRankingBlockSent,
  IRankingBlockReceived,
  IEndorserBlockGenerated,
  IEndorserBlockSent,
  IEndorserBlockReceived,
  ITransactionSent,
  ITransactionReceived,
} from "@/components/Sim/types";
import { useRef } from "react";
import { EConnectionState } from "@/contexts/SimContext/types";

// TODO: Replace with topology-based mapping
const HOST_PORT_TO_NODE: Record<string, string> = {
  // demo-burst
  "10.0.0.1:3001": "UpstreamNode",
  "10.0.0.2:3002": "Node0",
  "10.0.0.3:3003": "DownstreamNode",
  // demo-proto-devnet with TC
  "172.28.0.10:3001": "Node1",
  "172.28.0.20:3002": "Node2",
  "172.28.0.30:3003": "Node3",
  // demo-proto-devnet without TC
  "127.0.0.1:3001": "Node1",
  "127.0.0.1:3002": "Node2",
  "127.0.0.1:3003": "Node3",
  // docker immdb mock
  "172.28.0.110:3001": "UpstreamNode",
  "172.28.0.120:3002": "Node0",
  "172.28.0.130:3003": "DownstreamNode",
  // Add more mappings as needed
};

const getNodesFromConnection = (connectionId: string): [string, string] => {
  if (connectionId) {
    const endpoints = connectionId.split(" ");
    if (endpoints.length === 2) {
      return [HOST_PORT_TO_NODE[endpoints[0]], HOST_PORT_TO_NODE[endpoints[1]]];
    }
  }
  return ["UNKNOWN", "UNKNOWN"];
};

const parseRankingBlockGenerated = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // {"forgedBlock":{"newBlockHash":"c036...","newBlockSize":{"txCount":293,"txSize":{"txSizeBytes":88842},...},...},"kind":"TraceForgedBlock","slot":1561}
    if (log.kind === "TraceForgedBlock" && log.forgedBlock) {
      const block = log.forgedBlock;
      const txSizeBytes = block.newBlockSize?.txSize?.txSizeBytes ?? 0;

      const message: IRankingBlockGenerated = {
        type: EServerMessageType.RBGenerated,
        id: block.newBlockHash,
        slot: log.slot,
        producer: streamLabels.process,
        size_bytes: txSizeBytes,
        header_bytes: 0, // TODO: used? have we access to the header?
        endorsement: null,
        transactions: [], // TODO: used?
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse TraceForgedBlock log line:", logLine, error);
  }

  return null;
};

const parseRankingBlockSent = (
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=BlockFetch.Server.SendBlock
    // {"block": "23b021f8e2c06e64b10647d9eeb5c9f11e50181f5a569424e49f2448f6d5f8a8", "kind": "BlockFetchServer", "peer": {"connectionId": "10.0.0.2:3002 10.0.0.3:3003"}}
    if (log.kind === "BlockFetchServer" && log.peer && log.block) {
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

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
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

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
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // ns=BlockFetch.Client.CompletedBlockFetch
    // {"block":"56515bfd5751ca2c1ca0f21050cdb1cd020e396c623a16a2274528f643d4b5fd","delay":4985924.003937032,"kind":"CompletedBlockFetch","peer":{"connectionId":"127.0.0.1:3003 127.0.0.1:3002"},"size":862}
    if (log.kind === "CompletedBlockFetch" && log.peer && log.block) {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

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

const parseEndorserBlockGenerated = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // {"kind":"LeiosBlockForged","mempoolRestSize":304114,"numTxs":293,"slot":1311,"closureSize":88835,"ebSize":10844,"hash":"cb73e5ef..."}
    if (log.kind === "LeiosBlockForged") {
      const message: IEndorserBlockGenerated = {
        type: EServerMessageType.EBGenerated,
        id: log.hash,
        slot: log.slot,
        producer: streamLabels.process,
        size_bytes: log.ebSize,
        pipeline: 0, // XXX: unused
        transactions: [], // TODO: used?
        endorser_blocks: [], // XXX: not relevant for linear leios
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse LeiosBlockForged log line:", logLine, error);
  }

  return null;
};

const parseEndorserBlockSent = (
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
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const message: IEndorserBlockSent = {
        type: EServerMessageType.EBSent,
        slot: 0, // TODO: add slot (full point) to logs?
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
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=LeiosFetch.Remote.Receive.Block
    // {"kind":"Recv","msg":{"ebBytesSize":27471,"ebHash":"320648bc67a2a160bda3ca52cdf1fe05b3cee404da82fb98e5fa02b2fb970741","kind":"MsgLeiosBlock"},"mux_at":"2025-12-15T15:18:49.13935251Z","peer":{"connectionId":"10.0.0.2:3002 10.0.0.1:3001"}}
    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlock") {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

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

// HACK: plain enumeration of txs to emulate a sequence number on these messages
const nextTxId: Record<string, number> = {};

const parseTransactionSent = (
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
      const [sender, recipient] = getNodesFromConnection(
        log.peer?.connectionId || log.connectionId,
      );

      const txId = `${log.msg.ebHash}-${log.msg.bitmaps.reduce((acc: string, bitmap: any) => acc + bitmap, "")}`;

      const message: ITransactionSent = {
        type: EServerMessageType.TransactionSent,
        id: txId,
        sender,
        recipient,
        msg_size_bytes: log.msg.txsBytesSize,
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
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const log = JSON.parse(logLine);

    // From cardano-node ns=LeiosFetch.Remote.Receive.BlockTxs
    // {"mux_at":"2025-12-05T14:06:12.52499731Z","peer":{"connectionId":"127.0.0.1:3003 127.0.0.1:3002"},"kind":"Recv","msg":{"txsBytesSize":491520,"kind":"MsgLeiosBlockTxs","numTxs":30,"txs":"\u003celided\u003e"}}
    if (log.kind === "Recv" && log.msg && log.msg.kind === "MsgLeiosBlockTxs") {
      const [recipient, sender] = getNodesFromConnection(
        log.peer?.connectionId,
      );

      // FIXME: msg.txs is always elided
      const txId = nextTxId[recipient] || 0;
      nextTxId[recipient] = txId + 1;

      const message: ITransactionReceived = {
        type: EServerMessageType.TransactionReceived,
        id: txId.toString(),
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
    '{service="cardano-node"} |~ "BlockFetchServer|MsgBlock|CompletedBlockFetch|MsgLeiosBlock|MsgLeiosBlockTxs|LeiosBlockForged|TraceForgedBlock"';
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
                    parseRankingBlockGenerated(stream.stream, ts, logLine) ||
                    parseRankingBlockSent(ts, logLine) ||
                    parseRankingBlockReceived(ts, logLine) ||
                    parseEndorserBlockGenerated(stream.stream, ts, logLine) ||
                    parseEndorserBlockSent(ts, logLine) ||
                    parseEndorserBlockReceived(ts, logLine) ||
                    parseTransactionSent(ts, logLine) ||
                    parseTransactionReceived(ts, logLine);
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
