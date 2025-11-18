import { useSimContext } from "@/contexts/SimContext/context";
import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { TWorkerResponse } from "./worker";
import StreamWorker from "./worker?worker";

export const useStreamMessagesHandler = () => {
  const {
    state: { tracePath, aggregated, speedMultiplier },
    dispatch,
  } = useSimContext();
  const [streaming, setStreaming] = useState(false);
  const hasAutoStartedPlayback = useRef(false);

  const worker = useMemo(() => {
    return new StreamWorker();
  }, []);

  const startStream = useCallback(
    async (includeTransactions = false) => {
      // Reset timeline when starting new stream
      dispatch({ type: "RESET_TIMELINE" });
      setStreaming(true);
      hasAutoStartedPlayback.current = false;

      // Use worker
      worker.postMessage({
        type: "START",
        tracePath,
        aggregated,
        speedMultiplier,
        includeTransactions,
      });
    },
    [worker, tracePath, aggregated, speedMultiplier, dispatch],
  );

  const stopStream = useCallback(() => {
    // Stop worker
    worker.postMessage({ type: "STOP" });
    setStreaming(false);
  }, [worker]);

  useEffect(() => {
    worker.onmessage = (event: MessageEvent<TWorkerResponse>) => {
      const message = event.data;
      if (message.tracePath !== tracePath) {
        return;
      }
      if (message.type === "TIMELINE_EVENTS") {
        // Process batch of events in single dispatch
        dispatch({
          type: "ADD_TIMELINE_EVENT_BATCH",
          payload: message.events,
        });
        
        // Auto-start playback on first batch of events
        if (!hasAutoStartedPlayback.current) {
          hasAutoStartedPlayback.current = true;
          dispatch({ type: "SET_TIMELINE_PLAYING", payload: true });
        }
      }
      if (message.type === "DONE") {
        setStreaming(false);
      }
    };
    // if the tracePath changed, stop streaming
    worker.postMessage({ type: "STOP" });
    setStreaming(false);
  }, [worker, tracePath]);

  return useMemo(
    () => ({
      startStream,
      stopStream,
      streaming,
    }),
    [startStream, stopStream, streaming],
  );
};
