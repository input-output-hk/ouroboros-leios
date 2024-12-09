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
  const pendingPropagations = useRef<string[]>([]);
  const pendingMsgs = useRef<Map<number, IServerMessage[]>>(new Map());

  const startStream = useCallback(
    (startTime: number, range: number) => {
      const url = new URL("/api/messages/batch", window.location.href);
      url.searchParams.set("startTime", startTime.toString());
      url.searchParams.set("speed", range.toString());

      eventSource.current = new EventSource(url);
      eventSource.current.onmessage = function (message) {
        const json: IServerMessage = JSON.parse(message.data);
        const elapsed =
          simulationStartTime.current !== 0
            ? (performance.now() - simulationStartTime.current) * speed
            : 0;

        if (json.time / 1_000_000 < elapsed) {
          processMessage(json);
        } else {
          const otherEvents =
            pendingMsgs.current.get(json.time / 1_000_000) || [];
          pendingMsgs.current.set(json.time / 1_000_000, [
            ...otherEvents,
            json,
          ]);
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
        ? (performance.now() - simulationStartTime.current) * speed
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
      aggregatedData.current.total.txGenerated++;
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.publisher.toString(),
        "txGenerated",
      );
    } else if (message.type === EMessageType.TransactionSent) {
      aggregatedData.current.total.txSent++;
      incrementNodeAggregationData(
        aggregatedData.current.nodes,
        message.sender.toString(),
        "txSent",
      );
      pendingPropagations.current.push(
        `${message.sender}-${message.recipient}-${message.id}`,
      );
    } else if (message.type === EMessageType.TransactionReceived) {
      aggregatedData.current.total.txReceived++;
      const matchingSentIndex = pendingPropagations.current.indexOf(
        `${message.sender}-${message.recipient}-${message.id}`,
      );
      if (matchingSentIndex !== -1) {
        aggregatedData.current.total.txPropagations++;
        incrementNodeAggregationData(
          aggregatedData.current.nodes,
          message.recipient.toString(),
          "txReceived",
        );
        incrementNodeAggregationData(
          aggregatedData.current.nodes,
          message.sender.toString(),
          "txPropagations",
        );
        incrementNodeAggregationData(
          aggregatedData.current.nodes,
          message.recipient.toString(),
          "txPropagations",
        );
        pendingPropagations.current.splice(matchingSentIndex, 1);
      }
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
