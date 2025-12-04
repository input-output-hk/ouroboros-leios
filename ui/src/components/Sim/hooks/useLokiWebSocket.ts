import { useSimContext } from "@/contexts/SimContext/context";
import {
  IServerMessage,
  EServerMessageType,
  IRankingBlockSent,
} from "@/components/Sim/types";
import { useCallback, useEffect, useRef, useState } from "react";

// TODO: Replace with topology-based mapping
const HOST_PORT_TO_NODE: Record<string, string> = {
  "127.0.0.1:3001": "UpstreamNode",
  "127.0.0.1:3002": "Node0",
  "127.0.0.1:3003": "DownstreamNode",
  // Add more mappings as needed
};

const parseCardanoNodeLog = (
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
        id: `rb-${logData.prevCount + 1}`, // FIXME: use proper block hash
        sender,
        recipient,
      };

      return {
        time_s: timestamp,
        message,
      };
    }

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
    console.warn("Failed to parse log line:", logLine, error);
  }

  return null;
};

export const useLokiWebSocket = () => {
  const {
    state: { lokiHost },
    dispatch,
  } = useSimContext();
  const [connecting, setConnecting] = useState(false);
  const [connected, setConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  const connect = useCallback(() => {
    if (!lokiHost || connecting || connected) return;

    setConnecting(true);
    dispatch({ type: "RESET_TIMELINE" });

    try {
      // TODO: Multiple websockets instead? e.g. query={ns="BlockFetch.Client.CompletedBlockFetch"}
      const query = encodeURIComponent('{service="cardano-node"}');
      const wsUrl = `ws://${lokiHost}/loki/api/v1/tail?query=${query}&limit=10000`;
      console.log("Connecting to ", wsUrl);
      const ws = new WebSocket(wsUrl);
      wsRef.current = ws;

      let count = 0;
      ws.onopen = () => {
        setConnecting(false);
        setConnected(true);
        dispatch({ type: "SET_LOKI_CONNECTED", payload: true });
      };

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
                    console.debug("Stream value:", count, {
                      timestamp,
                      logLine,
                    });

                    const timestampSeconds = parseFloat(timestamp) / 1000000000;
                    const event = parseCardanoNodeLog(
                      stream.stream,
                      timestampSeconds,
                      logLine,
                    );
                    if (event) {
                      console.debug("Parsed", event.time_s, event.message);
                      events.push(event);
                    }
                  },
                );
              }
            });

            if (events.length > 0) {
              dispatch({
                type: "ADD_TIMELINE_EVENT_BATCH",
                payload: events,
              });
            }
          }
        } catch (error) {
          console.error("Error processing Loki message:", error);
        }
      };

      ws.onerror = (error) => {
        console.error("WebSocket error:", error);
        setConnecting(false);
        setConnected(false);
        dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
      };

      ws.onclose = () => {
        setConnecting(false);
        setConnected(false);
        dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
        wsRef.current = null;
      };
    } catch (error) {
      console.error("Failed to create WebSocket connection:", error);
      setConnecting(false);
      setConnected(false);
    }
  }, [lokiHost, connecting, connected, dispatch]);

  const disconnect = useCallback(() => {
    if (wsRef.current) {
      wsRef.current.close();
      wsRef.current = null;
    }
    setConnecting(false);
    setConnected(false);
    dispatch({ type: "SET_LOKI_CONNECTED", payload: false });
  }, [dispatch]);

  useEffect(() => {
    return () => {
      if (wsRef.current) {
        wsRef.current.close();
      }
    };
  }, []);

  return {
    connect,
    disconnect,
    connecting,
    connected,
  };
};
