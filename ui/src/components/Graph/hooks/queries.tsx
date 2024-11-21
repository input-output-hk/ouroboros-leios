import msgpack from "msgpack-lite";
import { Oboe } from "oboe";
import { useCallback, useEffect, useRef } from "react";

import { IGraphContextState } from "@/contexts/GraphContext/types";
import {
  EMessageType,
  ILink,
  INode,
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
  ITransformedNodeMap,
} from "../types";

export const useSetSimulationTimeHandler = ({
  setMaxTime,
}: IGraphContextState) => {
  const handleRequest = useCallback(() => {
    const url = new URL("/api/transactions/last", window.location.href);
    const time = fetch(url)
      .then((res) => res.json())
      .then((data: IServerMessage<ITransactionReceived>) => {
        setMaxTime(data.time / 1_000_000);
      });

    return time;
  }, []);

  return handleRequest;
};

export const useStreamMessagesHandler = ({
  setMessages,
  messages,
  setTransactions,
  currentTime
}: IGraphContextState) => {
  const debounceTimeoutRef = useRef<Timer | null>(null);
  const isAborted = useRef<boolean>(false);
  const oboeInstance = useRef<Oboe>();

  // Buffer to store prefetched data
  const prefetchBuffer = useRef<Set<IServerMessage>>(new Set());
  const isPrefetching = useRef<boolean>(false);

  const handleRequest = useCallback((time: number, buffer: Set<IServerMessage> | null = null) => {
    const url = new URL("/api/messages/batch", window.location.href);
    url.searchParams.set("time", time.toString());
    const result: Set<IServerMessage> = buffer || new Set();
    
    fetch(url).then(async res => {
      if (!res.body) {
        throw new Error("Not a stream.")
      }

      const reader = res.body.getReader();
      while(true) {
        const { done, value } = await reader.read();
        if (done || isAborted.current) {
          break;
        }

        const json = msgpack.decode(value);
        result.add(JSON.parse(json.toString()));

        // Debounce state updates
        if (!debounceTimeoutRef.current) {
          debounceTimeoutRef.current = setTimeout(() => {
            if (buffer) {
              // If fetching for prefetch, store in buffer
              prefetchBuffer.current = result;
              isPrefetching.current = false;
            } else {
              setMessages([...result]);
            }
            debounceTimeoutRef.current = null; // Clear the timeout
          }, 50);
        }
      }
    })
    // oboeInstance.current = oboe(url.toString()).node(
    //   "!",
    //   function (msg: IServerMessage) {
    //     if (isAborted.current) {
    //       // @ts-expect-error
    //       this.abort(); // Safely abort if marked as aborted
    //       return;
    //     }

    //     result.add(msg);

    //     // Debounce state updates
    //     if (!debounceTimeoutRef.current) {
    //       debounceTimeoutRef.current = setTimeout(() => {
    //         if (buffer) {
    //           // If fetching for prefetch, store in buffer
    //           prefetchBuffer.current = result;
    //           isPrefetching.current = false;
    //         } else {
    //           setMessages([...result]);
    //         }
    //         debounceTimeoutRef.current = null; // Clear the timeout
    //       }, 50);
    //     }

    //     return oboe.drop;
    //   },
    // );
  }, [setMessages]);

  // Function to initiate prefetch
  const prefetchNext = useCallback(
    (nextTime: number) => {
      if (isPrefetching.current || prefetchBuffer.current.size > 0) {
        // Already prefetching or buffer is full
        return;
      }
      isPrefetching.current = true;
      handleRequest(nextTime, prefetchBuffer.current);
    },
    [handleRequest]
  );

  // Function to clean prefetch buffer by removing entries before currentTime
  const cleanPrefetchBuffer = useCallback(() => {
    prefetchBuffer.current.forEach((msg) => {
      // Assuming `msg.time` is in the same unit as `currentTime` and represents the event time
      if (msg.time < currentTime) {
        prefetchBuffer.current.delete(msg);
      }
    });
  }, [currentTime]);

  // Main request handler with prefetching logic
  const requestWithPrefetch = useCallback(
    (time: number) => {
      // Clean the prefetch buffer before using it
      cleanPrefetchBuffer();

      // If there's prefetched data available, use it
      if (prefetchBuffer.current.size > 0) {
        setMessages([...prefetchBuffer.current]);
        prefetchBuffer.current = new Set();
        // After using prefetched data, prefetch the next chunk
        prefetchNext(time + 100); // Adjust the increment as per your time logic
      } else {
        // If no prefetched data, fetch normally and start prefetching
        handleRequest(time);
        prefetchNext(time + 100); // Adjust the increment as per your time logic
      }
    },
    [handleRequest, prefetchNext, setMessages]
  );

  useEffect(() => {
    const txGeneratedMessages =
      (messages?.filter(
        ({ message }) => message.type === EMessageType.TransactionGenerated,
      ) as IServerMessage<ITransactionGenerated>[]) || [];

    const txSentMessages =
      (messages?.filter(
        ({ message }) => message.type === EMessageType.TransactionSent,
      ) as IServerMessage<ITransactionSent>[]) || [];

    const txReceivedMessages =
      (messages?.filter(
        ({ message }) => message.type === EMessageType.TransactionReceived,
      ) as IServerMessage<ITransactionReceived>[]) || [];

    const transactionsById: Map<number, ITransactionMessage[]> = new Map();

    for (const generatedMsg of txGeneratedMessages) {
      const transactionList: ITransactionMessage[] = [];

      for (const sentMsg of txSentMessages) {
        if (sentMsg.message.id === generatedMsg.message.id) {
          const receivedMsg = txReceivedMessages.find(
            (r) =>
              r.message.id === generatedMsg.message.id &&
              r.message.sender === sentMsg.message.sender &&
              r.message.recipient === sentMsg.message.recipient,
          );

          if (!receivedMsg) {
            console.log(
              "Could not find matching transaction for " + sentMsg.message.id,
            );
            continue;
          }

          // Convert time from nanoseconds to miliseconds.
          transactionList.push({
            id: generatedMsg.message.id,
            duration:
              Math.floor(receivedMsg.time / 1_000_000) -
              Math.floor(sentMsg.time / 1_000_000),
            source: sentMsg.message.sender,
            target: sentMsg.message.recipient,
            sentTime: Math.floor(sentMsg.time / 1_000_000),
            generated: Math.floor(generatedMsg.time / 1_000_000),
          });
        }
      }

      if (transactionList.length) {
        transactionsById.set(generatedMsg.message.id, transactionList);
      }
    }

    setTransactions(transactionsById);
  }, [messages]);

  useEffect(() => {
    // Abort logic when `timestamp` changes
    return () => {
      if (debounceTimeoutRef.current) {
        clearTimeout(debounceTimeoutRef.current);
        debounceTimeoutRef.current = null;
      }
      isAborted.current = true; // Mark as aborted
      if (oboeInstance.current) {
        oboeInstance.current.abort(); // Abort the oboe instance
      }
    };
  }, []);

  return requestWithPrefetch;
};

export const useSetTopographyHandler = ({
  setTopography,
  setTopographyLoaded,
}: IGraphContextState) => {
  const handleRequest = useCallback(() => {
    fetch("/api/topography")
      .then((res) => res.json())
      .then((data: { links: ILink[]; nodes: INode[] }) => {
        const newResult: ITransformedNodeMap = {
          nodes: new Map(
            data.nodes.map((n, i) => [
              i,
              {
                data: n,
                fx: n.location[0],
                fy: n.location[1],
                id: i,
              },
            ]),
          ),
          links: new Map(
            data.links.map((l) => [
              `${l.nodes[0]}|${l.nodes[1]}`,
              {
                source: l.nodes[0],
                target: l.nodes[1],
              },
            ]),
          ),
        };

        setTopography(newResult);
      })
      .then(() => setTopographyLoaded(true));
  }, []);

  return handleRequest;
};
