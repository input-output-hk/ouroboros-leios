import { useSimContext } from "@/contexts/SimContext/context";
import {
  IServerMessage,
  EServerMessageType,
  IRankingBlockSent,
} from "@/components/Sim/types";
import { useCallback, useEffect, useRef, useState } from "react";

export const useLokiWebSocket = () => {
  const {
    state: { lokiHost },
    dispatch,
  } = useSimContext();
  const [connecting, setConnecting] = useState(false);
  const [connected, setConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  const parseUpstreamNodeLog = (
    logLine: string,
    timestamp: number,
  ): IServerMessage | null => {
    if (logLine.trim() === "MsgBlock") {
      // Hard-coded IRankingBlockSent for UpstreamNode -> Node0
      const message: IRankingBlockSent = {
        type: EServerMessageType.RBSent,
        slot: 0, // TODO: extract from actual data when available
        id: `rb-${timestamp}`,
        sender: "UpstreamNode",
        recipient: "Node0",
      };

      return {
        time_s: timestamp,
        message,
      };
    }

    return null;
  };

  const connect = useCallback(() => {
    if (!lokiHost || connecting || connected) return;

    setConnecting(true);
    dispatch({ type: "RESET_TIMELINE" });

    try {
      // TODO: find better queries
      const query = encodeURIComponent(
        '{service="immdb-server"} |= "MsgBlock"',
      );
      const wsUrl = `ws://${lokiHost}/loki/api/v1/tail?query=${query}`;
      console.log("Connecting to ", wsUrl);
      const ws = new WebSocket(wsUrl);
      wsRef.current = ws;

      ws.onopen = () => {
        setConnecting(false);
        setConnected(true);
        dispatch({ type: "SET_LOKI_CONNECTED", payload: true });
      };

      ws.onmessage = (event) => {
        try {
          const data = JSON.parse(event.data);
          console.log("Received Loki stream data:", data);

          if (data.streams && Array.isArray(data.streams)) {
            const events: IServerMessage[] = [];

            data.streams.forEach((stream: any) => {
              if (stream.values && Array.isArray(stream.values)) {
                stream.values.forEach(
                  ([timestamp, logLine]: [string, string]) => {
                    console.log("Stream value:", { timestamp, logLine });

                    const timestampSeconds = parseFloat(timestamp) / 1000000000;
                    const event = parseUpstreamNodeLog(
                      logLine,
                      timestampSeconds,
                    );

                    if (event) {
                      events.push(event);
                    }
                  },
                );
              }
            });

            if (events.length > 0) {
              console.log("Dispatching events:", events);
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
