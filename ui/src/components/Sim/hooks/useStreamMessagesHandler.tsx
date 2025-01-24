import { useCallback, useMemo, useRef, useState } from "react";

import { useSimContext } from "@/contexts/SimContext/context";
import { ISimulationAggregatedDataState } from "@/contexts/SimContext/types";

export const useStreamMessagesHandler = () => {
  const {
    state: {
      batchSize
    },
    dispatch
  } = useSimContext();
  const eventSource = useRef<EventSource>();
  const [streaming, setStreaming] = useState(false);

  const startStream = useCallback(() => {
    setStreaming(true);

    const url = new URL("/api/messages/batch", window.location.href);
    url.searchParams.set("batchSize", batchSize.toString());
    eventSource.current = new EventSource(url);
    eventSource.current.onerror = function (error) {
      stopStream();
    };

    eventSource.current.onmessage = function (message) {
      const json: ISimulationAggregatedDataState = JSON.parse(
        message.data,
        (key: string, v: any) => {
          if (key === "nodes") {
            return new Map(v);
          }

          return v;
        },
      );

      dispatch({ type: "SET_AGGREGATED_DATA", payload: json });
    };
  }, [batchSize]);

  const stopStream = useCallback(() => {
    eventSource.current?.close();
    setStreaming(false);
  }, []);

  return useMemo(
    () => ({
      startStream,
      stopStream,
      streaming,
    }),
    [startStream, stopStream, streaming],
  );
};
