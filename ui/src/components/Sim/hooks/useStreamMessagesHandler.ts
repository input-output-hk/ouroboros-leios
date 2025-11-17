import { useSimContext } from "@/contexts/SimContext/context";
import { useCallback, useEffect, useMemo, useState } from "react";
import { TWorkerResponse } from "./worker";
import StreamWorker from "./worker?worker";

export const useStreamMessagesHandler = () => {
  const {
    state: { tracePath, aggregated, batchSize, speedMultiplier },
    dispatch,
  } = useSimContext();
  const [streaming, setStreaming] = useState(false);

  const worker = useMemo(() => {
    return new StreamWorker();
  }, []);

  const startStream = useCallback(() => {
    // Reset timeline when starting new stream
    dispatch({ type: "RESET_TIMELINE" });
    
    worker.postMessage({
      type: "START",
      tracePath,
      aggregated,
      batchSize,
      speedMultiplier,
    });
    setStreaming(true);
  }, [worker, tracePath, aggregated, batchSize, speedMultiplier, dispatch]);

  const stopStream = useCallback(() => {
    worker.postMessage({ type: "STOP" });
    setStreaming(false);
  }, [worker]);

  useEffect(() => {
    worker.onmessage = (event: MessageEvent<TWorkerResponse>) => {
      const message = event.data;
      if (message.tracePath !== tracePath) {
        return;
      }
      if (message.type === "TIMELINE_EVENT") {
        dispatch({
          type: "ADD_TIMELINE_EVENT",
          payload: message.event,
        });
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
