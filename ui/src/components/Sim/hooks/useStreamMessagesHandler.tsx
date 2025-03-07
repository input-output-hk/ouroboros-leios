import { processMessage } from "@/components/Sim/hooks/utils";
import { useSimContext } from "@/contexts/SimContext/context";
import { ISimulationAggregatedDataState, ISimulationIntermediateDataState, TSimContextActions } from "@/contexts/SimContext/types";
import * as cbor from 'cbor';
import { Dispatch, useCallback, useEffect, useMemo, useState } from "react";
import { ReadableStream } from 'stream/web';
import { IServerMessage } from "../types";

const createEventStream = async (path: string, signal: AbortSignal): Promise<ReadableStream<IServerMessage>> => {
  const res = await fetch(path, { signal });
  if (!res.body) {
    throw new Error("body not streamed");
  }
  const transform = path.endsWith('.cbor') ? createCborTransformer() : createJsonTransformer();
  return res.body.pipeThrough(transform) as unknown as ReadableStream<IServerMessage>;
}

const createJsonTransformer = (): TransformStream<Uint8Array, IServerMessage> => {
  let buffer = "";
  const decoder = new TextDecoder();
  return new TransformStream({
    transform(chunk, controller) {
      buffer += decoder.decode(chunk);
      for (let nl = buffer.indexOf('\n'); nl != -1; nl = buffer.indexOf('\n')) {
        if (nl) {
          const message = JSON.parse(buffer.substring(0, nl));
          controller.enqueue(message);
        }
        buffer = buffer.substring(nl + 1);
      }
    }
  });
}

const createCborTransformer = (): TransformStream<Uint8Array, IServerMessage> => {
  let buffer: Buffer | null = null;
  return new TransformStream({
    transform(chunk, controller) {
      buffer = buffer ? Buffer.concat([buffer, chunk]) : Buffer.from(chunk);
      while (buffer != null) {
        try {
          const { value, unused } = cbor.decodeFirstSync(buffer, { extendedResults: true });
          buffer = unused as Buffer;
          controller.enqueue(value);
        } catch (error: any) {
          if (error.message === 'Insufficient data') {
            break;
          } else {
            throw error;
          }
        }
      }
    }
  })
}

const consumeStream = async (
  stream: ReadableStream<IServerMessage>,
  batchSize: number,
  dispatch: Dispatch<TSimContextActions>,
) => {
  const aggregatedData: ISimulationAggregatedDataState = {
    progress: 0,
    nodes: new Map(),
    global: {
      praosTxOnChain: 0,
      leiosTxOnChain: 0,
    },
    blocks: [],
    lastNodesUpdated: [],
  };
  const intermediate: ISimulationIntermediateDataState = {
    txs: [],
    leiosTxs: new Set(),
    praosTxs: new Set(),
    ibs: new Map(),
    ebs: new Map(),
    bytes: new Map(),
  };

  const nodesUpdated = new Set<string>();
  let batchEvents = 0;
  for await (const { time_s, message } of stream) {
    if (message.type.endsWith("Received") && "recipient" in message) {
      nodesUpdated.add(message.recipient);
    }
    if (message.type.endsWith("Sent") && "sender" in message) {
      nodesUpdated.add(message.sender);
    }
    if (message.type.endsWith("Generated") && "id" in message) {
      nodesUpdated.add(message.id);
    }
    processMessage({ time_s, message }, aggregatedData, intermediate);
    aggregatedData.progress = time_s;
    batchEvents++;
    if (batchEvents === batchSize) {
      dispatch({
        type: "SET_AGGREGATED_DATA",
        payload: {
          ...aggregatedData,
          lastNodesUpdated: [...nodesUpdated.values()],
        }
      });

      nodesUpdated.clear();
      batchEvents = 0;
    }
  }
  if (batchEvents) {
    dispatch({
      type: "SET_AGGREGATED_DATA",
      payload: {
        ...aggregatedData,
        lastNodesUpdated: [...nodesUpdated.values()],
      }
    });
  }
}

export const useStreamMessagesHandler = () => {
  const {
    state: {
      batchSize,
      tracePath,
    },
    dispatch
  } = useSimContext();
  const [streaming, setStreaming] = useState(false);

  const startStream = useCallback(() => {
    setStreaming(true);
  }, []);
  const stopStream = useCallback(() => {
    setStreaming(false);
  }, []);

  useEffect(() => {
    if (!streaming || !tracePath) {
      return;
    }

    const controller = new AbortController();
    createEventStream(tracePath, controller.signal)
      .then(stream => consumeStream(stream, batchSize, dispatch))
      .then(() => {
        setStreaming(false);
      })
      .catch(err => {
        if (err.name !== "AbortError") {
          throw err;
        }
      });
    return () => {
      controller.abort();
    };
  }, [streaming, tracePath]);

  return useMemo(
    () => ({
      startStream,
      stopStream,
      streaming,
    }),
    [startStream, stopStream, streaming],
  );
}