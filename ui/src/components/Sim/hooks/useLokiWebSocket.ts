import { useSimContext } from "@/contexts/SimContext/context";
import {
  IServerMessage,
  EServerMessageType,
  IRankingBlockSent,
  IRankingBlockReceived,
} from "@/components/Sim/types";
import { useRef } from "react";

interface QueryConfig {
  query: string;
  parser: (
    streamLabels: any,
    timestamp: number,
    logLine: string,
  ) => IServerMessage | null;
}

// FIXME: latency in topology is wrong

// TODO: Replace with topology-based mapping
const HOST_PORT_TO_NODE: Record<string, string> = {
  "127.0.0.1:3001": "UpstreamNode",
  "127.0.0.1:3002": "Node0",
  "127.0.0.1:3003": "DownstreamNode",
  // Add more mappings as needed
};

const parseBlockFetchServerLog = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const logData = JSON.parse(logLine);

    // Handle BlockFetchServer kind
    if (logData.kind === "BlockFetchServer" && logData.peer && logData.block) {
      // Extract sender from stream labels (process name)
      const sender = streamLabels.process;

      // Parse connection to extract recipient
      // connectionId format: "127.0.0.1:3002 127.0.0.1:3003"
      const connectionId = logData.peer.connectionId;
      let recipient = "Node0"; // fallback

      if (connectionId) {
        // Split connectionId to get both endpoints
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          // Second endpoint is the recipient
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0, // FIXME: Use proper slot number
        id: `rb-${logData.block.substring(0, 8)}`,
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse BlockFetchServer log line:", logLine, error);
  }

  return null;
};

const parseUpstreamNodeLog = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const logData = JSON.parse(logLine);

    // Handle MsgBlock with Send direction
    if (logData.msg === "MsgBlock" && logData.direction === "Send") {
      // Extract sender from stream labels (process name)
      const sender = streamLabels.process;

      // Parse connection to extract recipient
      // connectionId format: "127.0.0.1:3001 127.0.0.1:3002"
      const connectionId = logData.connectionId;
      let recipient = "Node0"; // fallback

      if (connectionId) {
        // Split connectionId to get both endpoints
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          // Second endpoint is the recipient
          const recipientEndpoint = endpoints[1];
          recipient = HOST_PORT_TO_NODE[recipientEndpoint] || recipient;
        }
      }

      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: logData.prevCount || 0, // FIXME: Use proper slot number
        id: `rb-upstream-${logData.prevCount + 1}`, // FIXME: use proper block hash
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }
  } catch (error) {
    console.warn("Failed to parse UpstreamNode log line:", logLine, error);
  }

  return null;
};

const parseCompletedBlockFetchLog = (
  streamLabels: any,
  timestamp: number,
  logLine: string,
): IServerMessage | null => {
  try {
    const logData = JSON.parse(logLine);

    // Handle CompletedBlockFetch kind
    if (
      logData.kind === "CompletedBlockFetch" &&
      logData.peer &&
      logData.block
    ) {
      // Extract recipient from stream labels (process name)
      const recipient = streamLabels.process;

      // Parse connection to extract sender
      // connectionId format: "127.0.0.1:3003 127.0.0.1:3002"
      const connectionId = logData.peer.connectionId;
      let sender = "Node0"; // fallback
      if (connectionId) {
        // Split connectionId to get both endpoints
        const endpoints = connectionId.split(" ");
        if (endpoints.length === 2) {
          const senderEndpoint = endpoints[1];
          sender = HOST_PORT_TO_NODE[senderEndpoint] || sender;
        }
      }

      const message: IRankingBlockReceived = {
        type: EServerMessageType.RBReceived,
        slot: 0, // FIXME: Use proper slot number
        id: `rb-${logData.block.substring(0, 8)}`,
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
      "Failed to parse CompletedBlockFetch log line:",
      logLine,
      error,
    );
  }

  return null;
};

// Query configurations
const QUERY_CONFIGS: QueryConfig[] = [
  {
    query: '{service="cardano-node", ns="BlockFetch.Server.SendBlock"}',
    parser: parseBlockFetchServerLog,
  },
  {
    query: '{service="cardano-node", process="UpstreamNode"} |= `MsgBlock`',
    parser: parseUpstreamNodeLog,
  },
  {
    query:
      '{service="cardano-node", ns="BlockFetch.Client.CompletedBlockFetch"}',
    parser: parseCompletedBlockFetchLog,
  },
];

function connectLokiWebSockets(lokiHost: string, dispatch: any): () => void {
  const websockets: WebSocket[] = [];
  let connectedCount = 0;

  dispatch({ type: "SET_LOKI_CONNECTED", payload: false });

  const createWebSocket = (config: QueryConfig, index: number): WebSocket => {
    const query = encodeURIComponent(config.query);
    const wsUrl = `ws://${lokiHost}/loki/api/v1/tail?query=${query}`;
    console.log(`Connecting with query ${index}:`, wsUrl);
    const ws = new WebSocket(wsUrl);

    let count = 0;
    ws.onopen = () => {
      connectedCount += 1;
      if (connectedCount === QUERY_CONFIGS.length) {
        dispatch({ type: "SET_LOKI_CONNECTED", payload: true });
      }
    };

    ws.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        console.debug(`Received Loki streams from query ${index}:`, data);

        if (data.streams && Array.isArray(data.streams)) {
          const events: IServerMessage[] = [];

          data.streams.forEach((stream: any) => {
            console.debug("Stream labels:", stream.stream);
            if (stream.values && Array.isArray(stream.values)) {
              stream.values.forEach(
                ([timestamp, logLine]: [string, string]) => {
                  count++;
                  console.debug(`Stream value from query ${index}:`, count, {
                    timestamp,
                    logLine,
                  });

                  const timestampSeconds = parseFloat(timestamp) / 1000000000;
                  const event = config.parser(
                    stream.stream,
                    timestampSeconds,
                    logLine,
                  );
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
          }
        }
      } catch (error) {
        console.error(
          `Error processing Loki message from query ${index}:`,
          error,
        );
      }
    };

    ws.onerror = (error) => {
      console.error(`WebSocket error for query ${index}:`, error);
      connectedCount = 0;
      dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
    };

    ws.onclose = () => {
      connectedCount = Math.max(0, connectedCount - 1);
      if (connectedCount === 0) {
        dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
      }
    };

    return ws;
  };

  try {
    QUERY_CONFIGS.forEach((config, index) => {
      websockets.push(createWebSocket(config, index));
    });
  } catch (error) {
    console.error("Failed to create WebSocket connections:", error);
    dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
  }

  // Return cleanup function
  return () => {
    websockets.forEach((ws) => {
      if (ws) {
        ws.close();
      }
    });
  };
}

export const useLokiWebSocket = () => {
  const {
    state: { lokiHost, lokiConnected },
    dispatch,
  } = useSimContext();
  const cleanupRef = useRef<(() => void) | null>(null);

  const connect = () => {
    if (!lokiHost || lokiConnected) return;

    dispatch({ type: "RESET_TIMELINE" });

    cleanupRef.current = connectLokiWebSockets(lokiHost, dispatch);
  };

  const disconnect = () => {
    cleanupRef.current?.();
    cleanupRef.current = null;
    dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
  };

  return { connect, disconnect };
};
