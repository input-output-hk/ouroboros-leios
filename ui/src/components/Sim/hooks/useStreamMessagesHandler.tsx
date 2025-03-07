import { useSimContext } from "@/contexts/SimContext/context";
import { useCallback, useEffect, useMemo, useState } from "react";
import { TWorkerResponse } from "./worker";

export const useStreamMessagesHandler = () => {
  const {
    state: {
      batchSize,
      tracePath,
    },
    dispatch
  } = useSimContext();
  const [streaming, setStreaming] = useState(false);

  const worker = useMemo(() => {
    if (typeof Worker === "undefined") {
      // return fake worker to make next.js happy
      return {
        postMessage() { }
      } as unknown as Worker;
    }
    return new Worker(new URL('worker.ts', import.meta.url));
  }, []);

  const startStream = useCallback(() => {
    worker.postMessage({
      type: "START",
      tracePath,
      batchSize,
    });
    setStreaming(true);
  }, [worker, tracePath, batchSize]);

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
      if (message.type === "EVENT") {
        dispatch({
          type: "SET_AGGREGATED_DATA",
          payload: message.aggregatedData,
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
}