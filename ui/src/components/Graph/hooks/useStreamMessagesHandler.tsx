import { useCallback, useMemo, useRef } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";
import { EMessageType, IServerMessage } from "../types";
import { incrementNodeAggregationData } from "../utils";

export const useStreamMessagesHandler = () => {
  const {
    state: { aggregatedData, simulationStartTime, speed },
  } = useGraphContext();
  const eventSource = useRef<EventSource>();
  const renderInterval = useRef<Timer | undefined>();
  const pendingMsgs = useRef<Map<number, IServerMessage[]>>(new Map());

  const startStream = useCallback(
    (startTime: number, range: number) => {
      console.log(pendingMsgs.current.size)
      const url = new URL("/api/messages/batch", window.location.href);
      url.searchParams.set("startTime", startTime.toString());
      url.searchParams.set("speed", range.toString());

      eventSource.current = new EventSource(url);
      eventSource.current.onmessage = function (message) {
        const json: IServerMessage = JSON.parse(message.data);
        const elapsed =
          simulationStartTime.current !== 0
            ? (Date.now() - simulationStartTime.current) * speed
            : 0;

        if (json.time / 1_000_000 < elapsed) {
          processMessage(json);
        } else {
          if (pendingMsgs.current.has(json.time / 1_000_000)) {
            pendingMsgs.current.get(json.time / 1_000_000)?.push(json);
          } else {
            pendingMsgs.current.set(json.time / 1_000_000, [json]);
          }
        }
      };

      renderInterval.current = setInterval(processMessagesIntervalFunc, 10);
    },
    [speed],
  );

  const stopStream = useCallback(() => {
    eventSource.current?.close();
    clearInterval(renderInterval.current);
  }, []);

  const processMessagesIntervalFunc = useCallback(() => {
    const elapsed =
      simulationStartTime.current !== 0
        ? (Date.now() - simulationStartTime.current) * speed
        : 0;

    for (const [time, data] of pendingMsgs.current) {
      if (time > elapsed) {
        break;
      }

      data.forEach(processMessage);
      pendingMsgs.current.delete(time);
    }
  }, [speed]);

  // Function to process each message and update transactions
  const processMessage = useCallback((json: IServerMessage) => {
    const { message } = json;

    if (message.type === EMessageType.TransactionGenerated) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.publisher.toString(),
        "txGenerated",
      );
    } else if (message.type === EMessageType.TransactionSent) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.sender.toString(),
        "txSent",
      );
    } else if (message.type === EMessageType.TransactionReceived) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.recipient.toString(),
        "txReceived",
      );
    } else if (message.type === EMessageType.InputBlockGenerated) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.producer.toString(),
        "ibGenerated",
      );
    } else if (message.type === EMessageType.InputBlockSent) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.sender.toString(),
        "ibSent",
      );
    } else if (message.type === EMessageType.InputBlockReceived) {
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.recipient.toString(),
        "ibReceived",
      );
    }
  }, []);

  return useMemo(
    () => ({
      startStream,
      stopStream,
    }),
    [startStream, stopStream],
  );
};
